// Squeeze: lossless PNG recompressor for make.fun png-squeeze-01 (Node 22, builtins only).
// Reads every /input/<id>/image.png, writes the smallest lossless PNG it can to /output/<id>/image.png.
// Strategy: decode to RGBA, try every exact colour-type form (palette orders, grey, RGB/RGBA, tRNS keys),
// screen fixed + adaptive filters and a band-wise filter search with zlib, then re-deflate the winner
// with an optimal-parsing deflate (cached LZ77 matches, DP parse, iterated Huffman, block-size search).
// Deterministic: fixed work budgets only, no clock, no randomness; the smallest candidate wins.
import { copyFileSync, mkdirSync, readdirSync, readFileSync, statSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { constants, deflateSync, inflateSync } from 'node:zlib';

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const SIG = Uint8Array.of(137, 80, 78, 71, 13, 10, 26, 10);
const CHAN = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 };

// ---------- checksums & chunk writing ----------
const CRC_TAB = (() => {
  const t = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    t[n] = c;
  }
  return t;
})();
function crc32(buf, start, end) {
  let c = -1;
  for (let i = start; i < end; i++) c = CRC_TAB[(c ^ buf[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}
function adler32(buf) {
  let a = 1;
  let b = 0;
  for (let i = 0; i < buf.length; ) {
    const stop = Math.min(buf.length, i + 5552);
    for (; i < stop; i++) {
      a += buf[i];
      b += a;
    }
    a %= 65521;
    b %= 65521;
  }
  return ((b << 16) | a) >>> 0;
}
function chunkBytes(type, data) {
  const out = new Uint8Array(12 + data.length);
  const v = new DataView(out.buffer);
  v.setUint32(0, data.length);
  for (let i = 0; i < 4; i++) out[4 + i] = type.charCodeAt(i);
  out.set(data, 8);
  v.setUint32(8 + data.length, crc32(out, 4, 8 + data.length));
  return out;
}
function ihdrData(w, h, ct) {
  const d = new Uint8Array(13);
  const v = new DataView(d.buffer);
  v.setUint32(0, w);
  v.setUint32(4, h);
  d[8] = 8;
  d[9] = ct;
  return d;
}
function assemblePng(w, h, form, zlibStream) {
  const parts = [SIG, chunkBytes('IHDR', ihdrData(w, h, form.ct))];
  if (form.plte) parts.push(chunkBytes('PLTE', form.plte));
  if (form.trns) parts.push(chunkBytes('tRNS', form.trns));
  parts.push(chunkBytes('IDAT', zlibStream));
  parts.push(chunkBytes('IEND', new Uint8Array(0)));
  let total = 0;
  for (const p of parts) total += p.length;
  const out = new Uint8Array(total);
  let at = 0;
  for (const p of parts) {
    out.set(p, at);
    at += p.length;
  }
  return out;
}
const formOverhead = (form) => (form.plte ? 12 + form.plte.length : 0) + (form.trns ? 12 + form.trns.length : 0);

// ---------- PNG decoding (the subset the contest checker reads) ----------
function paethPred(a, b, c) {
  const p = a + b - c;
  const pa = Math.abs(p - a);
  const pb = Math.abs(p - b);
  const pc = Math.abs(p - c);
  if (pa <= pb && pa <= pc) return a;
  return pb <= pc ? b : c;
}
function decodePng(bytes) {
  if (bytes.length < 8 || SIG.some((b, i) => bytes[i] !== b)) throw new Error('bad signature');
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = 8;
  let head = null;
  let palette = null;
  let trns = null;
  const idatParts = [];
  let sawEnd = false;
  while (at < bytes.length) {
    if (sawEnd) throw new Error('bytes after IEND');
    if (at + 12 > bytes.length) throw new Error('short chunk');
    const len = view.getUint32(at);
    if (len > 0x7fffffff || at + 12 + len > bytes.length) throw new Error('chunk overruns file');
    const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    if (crc32(bytes, at + 4, at + 8 + len) !== view.getUint32(at + 8 + len)) throw new Error('bad CRC');
    const data = bytes.subarray(at + 8, at + 8 + len);
    at += 12 + len;
    if (type === 'IHDR') {
      if (head) throw new Error('double IHDR');
      const dv = new DataView(data.buffer, data.byteOffset, 13);
      head = { w: dv.getUint32(0), h: dv.getUint32(4), depth: data[8], ct: data[9], comp: data[10], filt: data[11], inter: data[12] };
      if (!head.w || !head.h || head.depth !== 8 || !(head.ct in CHAN) || head.comp !== 0 || head.filt !== 0 || head.inter !== 0) {
        throw new Error('unsupported IHDR');
      }
    } else if (type === 'PLTE') {
      palette = data;
    } else if (type === 'tRNS') {
      trns = data;
    } else if (type === 'IDAT') {
      idatParts.push(Buffer.from(data));
    } else if (type === 'IEND') {
      sawEnd = true;
    } else {
      throw new Error('unexpected chunk ' + type);
    }
  }
  if (!head || !sawEnd || idatParts.length === 0) throw new Error('incomplete PNG');
  const bpp = CHAN[head.ct];
  const stride = head.w * bpp;
  const raw = inflateSync(Buffer.concat(idatParts), { maxOutputLength: head.h * (stride + 1) + 1 });
  if (raw.length !== head.h * (stride + 1)) throw new Error('inflated size mismatch');
  const samples = new Uint8Array(head.h * stride);
  for (let y = 0; y < head.h; y++) {
    const ft = raw[y * (stride + 1)];
    const src = y * (stride + 1) + 1;
    const dst = y * stride;
    const up = dst - stride;
    if (ft === 0) {
      samples.set(raw.subarray(src, src + stride), dst);
    } else if (ft === 1) {
      for (let i = 0; i < stride; i++) samples[dst + i] = raw[src + i] + (i >= bpp ? samples[dst + i - bpp] : 0);
    } else if (ft === 2) {
      for (let i = 0; i < stride; i++) samples[dst + i] = raw[src + i] + (y > 0 ? samples[up + i] : 0);
    } else if (ft === 3) {
      for (let i = 0; i < stride; i++) {
        samples[dst + i] = raw[src + i] + (((i >= bpp ? samples[dst + i - bpp] : 0) + (y > 0 ? samples[up + i] : 0)) >> 1);
      }
    } else if (ft === 4) {
      for (let i = 0; i < stride; i++) {
        const a = i >= bpp ? samples[dst + i - bpp] : 0;
        const b = y > 0 ? samples[up + i] : 0;
        const c = y > 0 && i >= bpp ? samples[up + i - bpp] : 0;
        samples[dst + i] = raw[src + i] + paethPred(a, b, c);
      }
    } else {
      throw new Error('bad filter ' + ft);
    }
  }
  const n = head.w * head.h;
  const rgba = new Uint8Array(n * 4);
  if (head.ct === 6) {
    rgba.set(samples);
  } else if (head.ct === 2) {
    const key = trns ? (trns[1] << 16) | (trns[3] << 8) | trns[5] : -1;
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 3, d += 4) {
      rgba[d] = samples[s];
      rgba[d + 1] = samples[s + 1];
      rgba[d + 2] = samples[s + 2];
      rgba[d + 3] = ((samples[s] << 16) | (samples[s + 1] << 8) | samples[s + 2]) === key ? 0 : 255;
    }
  } else if (head.ct === 0) {
    const key = trns ? trns[1] : -1;
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const g = samples[i];
      rgba[d] = g;
      rgba[d + 1] = g;
      rgba[d + 2] = g;
      rgba[d + 3] = g === key ? 0 : 255;
    }
  } else if (head.ct === 4) {
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 2, d += 4) {
      rgba[d] = samples[s];
      rgba[d + 1] = samples[s];
      rgba[d + 2] = samples[s];
      rgba[d + 3] = samples[s + 1];
    }
  } else {
    if (!palette) throw new Error('palette missing');
    const entries = palette.length / 3;
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const e = samples[i];
      if (e >= entries) throw new Error('palette index out of range');
      rgba[d] = palette[e * 3];
      rgba[d + 1] = palette[e * 3 + 1];
      rgba[d + 2] = palette[e * 3 + 2];
      rgba[d + 3] = trns && e < trns.length ? trns[e] : 255;
    }
  }
  return { rgba, w: head.w, h: head.h };
}

// ---------- image analysis & exact forms ----------
function analyseImage(rgba) {
  const n = rgba.length >>> 2;
  let opaque = true;
  let grey = true;
  const byWord = new Map();
  let overflow = false;
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    const r = rgba[d];
    const g = rgba[d + 1];
    const b = rgba[d + 2];
    const a = rgba[d + 3];
    if (a !== 255) opaque = false;
    if (r !== g || r !== b) grey = false;
    if (!overflow) {
      const word = (r | (g << 8) | (b << 16) | (a << 24)) >>> 0;
      const hit = byWord.get(word);
      if (hit) hit.count++;
      else if (byWord.size >= 256) overflow = true;
      else byWord.set(word, { r, g, b, a, word, count: 1, first: i });
    }
  }
  return { opaque, grey, colours: overflow ? null : [...byWord.values()] };
}
function singleTransparentKey(rgba, grey) {
  let key = -1;
  for (let d = 0; d < rgba.length; d += 4) {
    const a = rgba[d + 3];
    if (a === 255) continue;
    if (a !== 0) return null;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (key === -1) key = v;
    else if (key !== v) return null;
  }
  if (key === -1) return null;
  for (let d = 0; d < rgba.length; d += 4) {
    if (rgba[d + 3] !== 255) continue;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (v === key) return null;
  }
  return key;
}
function samplesFor(rgba, ct) {
  if (ct === 6) return rgba;
  const n = rgba.length >>> 2;
  const ch = CHAN[ct];
  const out = new Uint8Array(n * ch);
  for (let i = 0, d = 0, s = 0; i < n; i++, d += 4, s += ch) {
    if (ct === 0) out[s] = rgba[d];
    else if (ct === 4) {
      out[s] = rgba[d];
      out[s + 1] = rgba[d + 3];
    } else {
      out[s] = rgba[d];
      out[s + 1] = rgba[d + 1];
      out[s + 2] = rgba[d + 2];
    }
  }
  return out;
}
function paletteForm(rgba, colours, order) {
  const lum = (c) => 299 * c.r + 587 * c.g + 114 * c.b;
  const sorted = [...colours].sort((x, y) => {
    const tx = x.a === 255 ? 1 : 0;
    const ty = y.a === 255 ? 1 : 0;
    if (tx !== ty) return tx - ty;
    if (tx === 0 && x.a !== y.a) return x.a - y.a;
    if (order === 'luminance') return lum(x) - lum(y) || x.word - y.word;
    if (order === 'first') return x.first - y.first || x.word - y.word;
    return y.count - x.count || x.word - y.word;
  });
  const indexOf = new Map(sorted.map((c, i) => [c.word, i]));
  const plte = new Uint8Array(sorted.length * 3);
  let lastClear = 0;
  sorted.forEach((c, i) => {
    plte[i * 3] = c.r;
    plte[i * 3 + 1] = c.g;
    plte[i * 3 + 2] = c.b;
    if (c.a !== 255) lastClear = i + 1;
  });
  const trns = lastClear === 0 ? null : Uint8Array.from(sorted.slice(0, lastClear), (c) => c.a);
  const n = rgba.length >>> 2;
  const indices = new Uint8Array(n);
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    const word = (rgba[d] | (rgba[d + 1] << 8) | (rgba[d + 2] << 16) | (rgba[d + 3] << 24)) >>> 0;
    indices[i] = indexOf.get(word);
  }
  return { ct: 3, bpp: 1, samples: indices, plte, trns, tag: 'pal-' + order };
}
function formsFor(rgba) {
  const info = analyseImage(rgba);
  const forms = [];
  if (info.colours) {
    for (const order of ['count', 'luminance', 'first']) forms.push(paletteForm(rgba, info.colours, order));
    if (!info.grey) return forms;
  }
  const key = info.opaque ? null : singleTransparentKey(rgba, info.grey);
  let ct;
  let trns = null;
  if (info.grey) {
    ct = info.opaque || key !== null ? 0 : 4;
    if (key !== null) trns = Uint8Array.of(0, key);
  } else {
    ct = info.opaque || key !== null ? 2 : 6;
    if (key !== null) trns = Uint8Array.of(0, (key >>> 16) & 0xff, 0, (key >>> 8) & 0xff, 0, key & 0xff);
  }
  forms.push({ ct, bpp: CHAN[ct], samples: samplesFor(rgba, ct), plte: null, trns, tag: 'ct' + ct });
  return forms;
}

// ---------- PNG filters ----------
function filterRowInto(type, cur, prev, bpp, out) {
  const n = cur.length;
  if (type === 0) out.set(cur);
  else if (type === 1) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0);
  } else if (type === 2) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (prev ? prev[i] : 0);
  } else if (type === 3) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (((i >= bpp ? cur[i - bpp] : 0) + (prev ? prev[i] : 0)) >> 1);
  } else {
    for (let i = 0; i < n; i++) {
      const a = i >= bpp ? cur[i - bpp] : 0;
      const b = prev ? prev[i] : 0;
      const c = prev && i >= bpp ? prev[i - bpp] : 0;
      out[i] = cur[i] - paethPred(a, b, c);
    }
  }
}
function signedSum(row) {
  let s = 0;
  for (let i = 0; i < row.length; i++) {
    const v = row[i];
    s += v < 128 ? v : 256 - v;
  }
  return s;
}
const FILTER_CHOICES = [0, 1, 2, 4, 'minsum', 'pairs'];
const BAND_CHOICES = [0, 1, 2, 4, 'pairs'];
function filterBand(samples, w, bpp, y0, y1, choice, seen, stampRef, counts, trial) {
  const stride = w * bpp;
  const rows = y1 - y0;
  const raw = new Uint8Array(rows * (stride + 1));
  for (let y = y0; y < y1; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    const at = (y - y0) * (stride + 1);
    if (typeof choice === 'number') {
      raw[at] = choice;
      filterRowInto(choice, cur, prev, bpp, raw.subarray(at + 1, at + 1 + stride));
      continue;
    }
    let bestType = 0;
    let bestCost = Infinity;
    for (let t = 0; t < 5; t++) {
      filterRowInto(t, cur, prev, bpp, trial);
      let cost;
      if (choice === 'minsum') {
        cost = signedSum(trial);
      } else if (choice === 'entropy') {
        counts.fill(0);
        for (let i = 0; i < stride; i++) counts[trial[i]]++;
        let e = 0;
        for (let i = 0; i < 256; i++) {
          if (counts[i]) {
            const p = counts[i] / stride;
            e -= p * Math.log2(p);
          }
        }
        cost = e;
      } else {
        stampRef.v++;
        const stamp = stampRef.v;
        let distinct = 0;
        for (let i = 1; i < stride; i++) {
          const pair = (trial[i - 1] << 8) | trial[i];
          if (seen[pair] !== stamp) {
            seen[pair] = stamp;
            distinct++;
          }
        }
        cost = distinct;
      }
      if (cost < bestCost) {
        bestCost = cost;
        bestType = t;
      }
    }
    raw[at] = bestType;
    filterRowInto(bestType, cur, prev, bpp, raw.subarray(at + 1, at + 1 + stride));
  }
  return raw;
}
function filterWhole(samples, w, h, bpp, choice) {
  const seen = new Uint32Array(65536);
  const stampRef = { v: 0 };
  const counts = new Int32Array(256);
  const trial = new Uint8Array(w * bpp);
  return filterBand(samples, w, bpp, 0, h, choice, seen, stampRef, counts, trial);
}
function bandSearchRaw(samples, w, h, bpp, bandRows) {
  const seen = new Uint32Array(65536);
  const stampRef = { v: 0 };
  const counts = new Int32Array(256);
  const trial = new Uint8Array(w * bpp);
  const parts = [];
  let tail = new Uint8Array(0);
  for (let y0 = 0; y0 < h; y0 += bandRows) {
    const y1 = Math.min(h, y0 + bandRows);
    let bestRaw = null;
    let bestLen = Infinity;
    for (const choice of BAND_CHOICES) {
      const cand = filterBand(samples, w, bpp, y0, y1, choice, seen, stampRef, counts, trial);
      const z =
        tail.length > 0
          ? deflateSync(cand, { level: 6, memLevel: 8, dictionary: tail })
          : deflateSync(cand, { level: 6, memLevel: 8 });
      if (z.length < bestLen) {
        bestLen = z.length;
        bestRaw = cand;
      }
    }
    parts.push(bestRaw);
    const joined = new Uint8Array(tail.length + bestRaw.length);
    joined.set(tail);
    joined.set(bestRaw, tail.length);
    tail = joined.subarray(Math.max(0, joined.length - 32768));
  }
  const out = new Uint8Array(h * (w * bpp + 1));
  let off = 0;
  for (const p of parts) {
    out.set(p, off);
    off += p.length;
  }
  return out;
}

// ---------- length-limited Huffman (heap tree + Kraft-unit limiting) ----------
function huffmanLengths(freq, maxLen) {
  const n = freq.length;
  const lengths = new Array(n).fill(0);
  const usedIdx = [];
  for (let i = 0; i < n; i++) if (freq[i] > 0) usedIdx.push(i);
  if (usedIdx.length === 0) return lengths;
  if (usedIdx.length === 1) {
    lengths[usedIdx[0]] = 1;
    return lengths;
  }
  const heap = [];
  let seq = 0;
  const less = (a, b) => a.w < b.w || (a.w === b.w && a.seq < b.seq);
  const push = (node) => {
    heap.push(node);
    let i = heap.length - 1;
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!less(heap[i], heap[p])) break;
      const tmp = heap[i];
      heap[i] = heap[p];
      heap[p] = tmp;
      i = p;
    }
  };
  const pop = () => {
    const top = heap[0];
    const last = heap.pop();
    if (heap.length) {
      heap[0] = last;
      let i = 0;
      for (;;) {
        const l = 2 * i + 1;
        const r = l + 1;
        let m = i;
        if (l < heap.length && less(heap[l], heap[m])) m = l;
        if (r < heap.length && less(heap[r], heap[m])) m = r;
        if (m === i) break;
        const tmp = heap[i];
        heap[i] = heap[m];
        heap[m] = tmp;
        i = m;
      }
    }
    return top;
  };
  for (const i of usedIdx) push({ w: freq[i], sym: i, left: null, right: null, seq: seq++ });
  while (heap.length > 1) {
    const a = pop();
    const b = pop();
    push({ w: a.w + b.w, sym: -1, left: a, right: b, seq: seq++ });
  }
  const walk = (node, d) => {
    if (node.sym >= 0) {
      lengths[node.sym] = d;
      return;
    }
    walk(node.left, d + 1);
    walk(node.right, d + 1);
  };
  walk(heap[0], 0);
  let maxActual = 0;
  for (const i of usedIdx) if (lengths[i] > maxActual) maxActual = lengths[i];
  if (maxActual <= maxLen) return lengths;
  for (const i of usedIdx) if (lengths[i] > maxLen) lengths[i] = maxLen;
  const unit = (l) => 2 ** (maxLen - l);
  let excess = -(2 ** maxLen);
  for (const i of usedIdx) excess += unit(lengths[i]);
  let guard = 0;
  while (excess > 0 && guard++ < 100000) {
    let best = -1;
    for (const i of usedIdx) {
      if (lengths[i] >= maxLen) continue;
      const r = 2 ** (maxLen - lengths[i] - 1);
      if (r > excess) continue;
      if (
        best < 0 ||
        freq[i] < freq[best] ||
        (freq[i] === freq[best] && (lengths[i] > lengths[best] || (lengths[i] === lengths[best] && i > best)))
      ) {
        best = i;
      }
    }
    if (best >= 0) {
      excess -= 2 ** (maxLen - lengths[best] - 1);
      lengths[best]++;
      continue;
    }
    let m = -1;
    for (const i of usedIdx) if (lengths[i] < maxLen && lengths[i] > m) m = lengths[i];
    if (m < 0) break;
    let shortPick = -1;
    let longPick = -1;
    for (const i of usedIdx) {
      if (lengths[i] === maxLen && (shortPick < 0 || freq[i] < freq[shortPick] || (freq[i] === freq[shortPick] && i > shortPick))) shortPick = i;
      if (lengths[i] === m && (longPick < 0 || freq[i] < freq[longPick] || (freq[i] === freq[longPick] && i > longPick))) longPick = i;
    }
    if (shortPick < 0 || longPick < 0) break;
    excess += unit(m + 1) - unit(maxLen);
    lengths[shortPick] = m + 1;
    excess -= 2 ** (maxLen - m - 1);
    lengths[longPick] = m + 1;
  }
  if (excess !== 0) {
    const k = usedIdx.length;
    const d = Math.ceil(Math.log2(k));
    const atShallow = 2 ** d - k;
    const sorted = [...usedIdx].sort((a, b) => freq[b] - freq[a] || a - b);
    sorted.forEach((sym, idx) => {
      lengths[sym] = idx < atShallow ? d - 1 : d;
    });
    if (d === 0) lengths[sorted[0]] = 1;
  }
  return lengths;
}
function ensureTwoCodes(lengths) {
  let used = 0;
  let first = -1;
  for (let i = 0; i < lengths.length; i++) {
    if (lengths[i] > 0) {
      used++;
      if (first < 0) first = i;
    }
  }
  if (used === 0) {
    lengths[0] = 1;
    lengths[1] = 1;
  } else if (used === 1) {
    lengths[first === 0 ? 1 : 0] = 1;
  }
  return lengths;
}
function canonicalCodes(lengths) {
  let maxBits = 0;
  for (const l of lengths) if (l > maxBits) maxBits = l;
  const blCount = new Array(maxBits + 1).fill(0);
  for (const l of lengths) if (l) blCount[l]++;
  const nextCode = new Array(maxBits + 1).fill(0);
  let code = 0;
  for (let bits = 1; bits <= maxBits; bits++) {
    code = (code + blCount[bits - 1]) << 1;
    nextCode[bits] = code;
  }
  const codes = new Array(lengths.length).fill(0);
  for (let i = 0; i < lengths.length; i++) if (lengths[i]) codes[i] = nextCode[lengths[i]]++;
  return codes;
}
function reversed(code, len) {
  let r = 0;
  for (let i = 0; i < len; i++) {
    r = (r << 1) | (code & 1);
    code >>>= 1;
  }
  return r;
}

// ---------- optimal-parsing deflate ----------
const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
const CL_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
const LEN_SYM = new Int32Array(259);
const LEN_XB = new Int32Array(259);
const LEN_XV = new Int32Array(259);
for (let l = 3; l <= 258; l++) {
  let s = 0;
  if (l === 258) s = 28;
  else {
    for (let i = 0; i < 28; i++) {
      if (LEN_BASE[i] <= l) s = i;
      else break;
    }
  }
  LEN_SYM[l] = 257 + s;
  LEN_XB[l] = LEN_EXTRA[s];
  LEN_XV[l] = l - LEN_BASE[s];
}
const DIST_SYM = new Int32Array(32769);
const DIST_XB = new Int32Array(32769);
const DIST_XV = new Int32Array(32769);
for (let d = 1; d <= 32768; d++) {
  let s = 0;
  for (let i = 0; i < 30; i++) {
    if (DIST_BASE[i] <= d) s = i;
    else break;
  }
  DIST_SYM[d] = s;
  DIST_XB[d] = DIST_EXTRA[s];
  DIST_XV[d] = d - DIST_BASE[s];
}
const LEN_BOUNDS = [35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];

function computeMatches(data, maxChain) {
  const n = data.length;
  const bestLen = new Int32Array(n);
  const bestDist = new Int32Array(n);
  const HASH_SIZE = 1 << 15;
  const HASH_MASK = HASH_SIZE - 1;
  const head = new Int32Array(HASH_SIZE).fill(-1);
  const prev = new Int32Array(n).fill(-1);
  for (let i = 0; i < n; i++) {
    if (i + 2 >= n) break;
    const h = ((data[i] << 10) ^ (data[i + 1] << 5) ^ data[i + 2]) & HASH_MASK;
    let cand = head[h];
    let bl = 0;
    let bd = 0;
    let chain = 0;
    const maxLen = Math.min(258, n - i);
    while (cand >= 0 && chain < maxChain) {
      const dist = i - cand;
      if (dist > 32768) break;
      if (bl === 0 || (bl < maxLen && data[cand + bl] === data[i + bl])) {
        let l = 0;
        while (l < maxLen && data[cand + l] === data[i + l]) l++;
        if (l >= 3 && (l > bl || (l === bl && dist < bd))) {
          bl = l;
          bd = dist;
          if (l >= maxLen) break;
        }
      }
      cand = prev[cand];
      chain++;
    }
    bestLen[i] = bl;
    bestDist[i] = bd;
    prev[i] = head[h];
    head[h] = i;
  }
  return { bestLen, bestDist };
}
function parseWithMatches(data, matches, litCost, lenCost, distCost) {
  const n = data.length;
  const { bestLen, bestDist } = matches;
  const dp = new Float64Array(n + 1).fill(Infinity);
  const fromPos = new Int32Array(n + 1).fill(-1);
  const fromLen = new Int32Array(n + 1);
  const fromDist = new Int32Array(n + 1);
  dp[0] = 0;
  for (let i = 0; i < n; i++) {
    const base = dp[i];
    if (base === Infinity) continue;
    const lc = base + litCost[data[i]];
    if (lc < dp[i + 1]) {
      dp[i + 1] = lc;
      fromPos[i + 1] = i;
      fromLen[i + 1] = 0;
      fromDist[i + 1] = 0;
    }
    const bl = bestLen[i];
    if (bl >= 3) {
      const bd = bestDist[i];
      const dc = distCost[bd];
      const small = Math.min(bl, 32);
      for (let l = 3; l <= small; l++) {
        const c = base + lenCost[l] + dc;
        if (c < dp[i + l]) {
          dp[i + l] = c;
          fromPos[i + l] = i;
          fromLen[i + l] = l;
          fromDist[i + l] = bd;
        }
      }
      if (bl > 32) {
        for (const l of LEN_BOUNDS) {
          if (l <= 32 || l > bl) continue;
          const c = base + lenCost[l] + dc;
          if (c < dp[i + l]) {
            dp[i + l] = c;
            fromPos[i + l] = i;
            fromLen[i + l] = l;
            fromDist[i + l] = bd;
          }
        }
        const c = base + lenCost[bl] + dc;
        if (c < dp[i + bl]) {
          dp[i + bl] = c;
          fromPos[i + bl] = i;
          fromLen[i + bl] = bl;
          fromDist[i + bl] = bd;
        }
      }
    }
  }
  const syms = [];
  let p = n;
  while (p > 0) {
    const j = fromPos[p];
    if (j < 0) throw new Error('parse gap');
    if (fromLen[p] === 0) syms.push({ lit: data[j] });
    else syms.push({ len: fromLen[p], dist: fromDist[p] });
    p = j;
  }
  syms.reverse();
  return syms;
}
function freqsOf(syms) {
  const litFreq = new Array(288).fill(0);
  const distFreq = new Array(30).fill(0);
  for (const s of syms) {
    if (s.lit !== undefined) litFreq[s.lit]++;
    else {
      litFreq[LEN_SYM[s.len]]++;
      distFreq[DIST_SYM[s.dist]]++;
    }
  }
  litFreq[256] = 1;
  return { litFreq, distFreq };
}
function costsFromLengths(litLen, distLen) {
  const litCost = new Float64Array(256);
  for (let i = 0; i < 256; i++) litCost[i] = litLen[i] || 16;
  const lenCost = new Float64Array(259);
  for (let l = 3; l <= 258; l++) lenCost[l] = (litLen[LEN_SYM[l]] || 16) + LEN_XB[l];
  const distCost = new Float64Array(32769);
  for (let d = 1; d <= 32768; d++) distCost[d] = (distLen[DIST_SYM[d]] || 16) + DIST_XB[d];
  return { litCost, lenCost, distCost };
}
class BitWriter {
  constructor() {
    this.bytes = [];
    this.buf = 0;
    this.nbits = 0;
  }
  writeBits(value, count) {
    this.buf |= value << this.nbits;
    this.nbits += count;
    while (this.nbits >= 8) {
      this.bytes.push(this.buf & 0xff);
      this.buf >>>= 8;
      this.nbits -= 8;
    }
  }
  writeCode(code, len) {
    this.writeBits(reversed(code, len), len);
  }
  finish() {
    if (this.nbits > 0) {
      this.bytes.push(this.buf & 0xff);
      this.buf = 0;
      this.nbits = 0;
    }
    return Uint8Array.from(this.bytes);
  }
}
function rleLengths(seq) {
  const out = [];
  let i = 0;
  while (i < seq.length) {
    const v = seq[i];
    let run = 1;
    while (i + run < seq.length && seq[i + run] === v) run++;
    if (v === 0) {
      let r = run;
      while (r >= 11) {
        const take = Math.min(r, 138);
        out.push([18, take - 11, 7]);
        r -= take;
      }
      if (r >= 3) {
        out.push([17, r - 3, 3]);
        r = 0;
      }
      while (r-- > 0) out.push([0, 0, 0]);
    } else {
      out.push([v, 0, 0]);
      let r = run - 1;
      while (r >= 3) {
        const take = Math.min(r, 6);
        out.push([16, take - 3, 2]);
        r -= take;
      }
      while (r-- > 0) out.push([v, 0, 0]);
    }
    i += run;
  }
  return out;
}
function emitDynamicBlock(bw, syms, litLengths, distLengths, isFinal) {
  const litCodes = canonicalCodes(litLengths);
  const distCodes = canonicalCodes(distLengths);
  let hlit = 288;
  while (hlit > 257 && litLengths[hlit - 1] === 0) hlit--;
  let hdist = 30;
  while (hdist > 1 && distLengths[hdist - 1] === 0) hdist--;
  const seq = litLengths.slice(0, hlit).concat(distLengths.slice(0, hdist));
  const rle = rleLengths(seq);
  const clFreq = new Array(19).fill(0);
  for (const [s] of rle) clFreq[s]++;
  const clLengths = ensureTwoCodes(huffmanLengths(clFreq, 7));
  const clCodes = canonicalCodes(clLengths);
  let hclen = 19;
  while (hclen > 4 && clLengths[CL_ORDER[hclen - 1]] === 0) hclen--;
  bw.writeBits(isFinal ? 1 : 0, 1);
  bw.writeBits(2, 2);
  bw.writeBits(hlit - 257, 5);
  bw.writeBits(hdist - 1, 5);
  bw.writeBits(hclen - 4, 4);
  for (let i = 0; i < hclen; i++) bw.writeBits(clLengths[CL_ORDER[i]], 3);
  for (const [s, xv, xb] of rle) {
    bw.writeCode(clCodes[s], clLengths[s]);
    if (xb) bw.writeBits(xv, xb);
  }
  for (const s of syms) {
    if (s.lit !== undefined) {
      bw.writeCode(litCodes[s.lit], litLengths[s.lit]);
    } else {
      const ls = LEN_SYM[s.len];
      bw.writeCode(litCodes[ls], litLengths[ls]);
      if (LEN_XB[s.len]) bw.writeBits(LEN_XV[s.len], LEN_XB[s.len]);
      const ds = DIST_SYM[s.dist];
      bw.writeCode(distCodes[ds], distLengths[ds]);
      if (DIST_XB[s.dist]) bw.writeBits(DIST_XV[s.dist], DIST_XB[s.dist]);
    }
  }
  bw.writeCode(litCodes[256], litLengths[256]);
}
function deflateOptimal(data, iterations, maxChain) {
  if (data.length === 0) return Uint8Array.of(0x78, 0x9c, 0x01, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01);
  const matches = computeMatches(data, maxChain);
  let litLen = new Array(288);
  for (let i = 0; i < 288; i++) litLen[i] = i < 144 ? 8 : i < 256 ? 9 : i < 280 ? 7 : 8;
  let distLen = new Array(30).fill(5);
  let syms = null;
  for (let it = 0; it < iterations; it++) {
    const c = costsFromLengths(litLen, distLen);
    syms = parseWithMatches(data, matches, c.litCost, c.lenCost, c.distCost);
    const f = freqsOf(syms);
    litLen = ensureTwoCodes(huffmanLengths(f.litFreq, 15));
    distLen = ensureTwoCodes(huffmanLengths(f.distFreq, 15));
  }
  const emit = (blockBytes) => {
    const bw = new BitWriter();
    if (blockBytes > 0 && data.length > blockBytes) {
      const blocks = [];
      let cur = [];
      let covered = 0;
      for (const s of syms) {
        cur.push(s);
        covered += s.lit !== undefined ? 1 : s.len;
        if (covered >= blockBytes) {
          blocks.push(cur);
          cur = [];
          covered = 0;
        }
      }
      if (cur.length) blocks.push(cur);
      blocks.forEach((bs, bi) => {
        const f = freqsOf(bs);
        const ll = ensureTwoCodes(huffmanLengths(f.litFreq, 15));
        const dl = ensureTwoCodes(huffmanLengths(f.distFreq, 15));
        emitDynamicBlock(bw, bs, ll, dl, bi === blocks.length - 1);
      });
    } else {
      emitDynamicBlock(bw, syms, litLen, distLen, true);
    }
    const def = bw.finish();
    const out = new Uint8Array(2 + def.length + 4);
    out[0] = 0x78;
    out[1] = 0x9c;
    out.set(def, 2);
    new DataView(out.buffer).setUint32(2 + def.length, adler32(data));
    return out;
  };
  let best = null;
  for (const bb of [0, 65536, 131072, 262144]) {
    const cand = emit(bb);
    if (best === null || cand.length < best.length) best = cand;
  }
  return best;
}

// ---------- per-image squeeze ----------
function squeezeImage(rgba, w, h) {
  const forms = formsFor(rgba);
  // Stage 1: screen every (form, filter) at zlib level 6.
  const screened = [];
  for (const form of forms) {
    for (const choice of FILTER_CHOICES) {
      const raw = filterWhole(form.samples, w, h, form.bpp, choice);
      const z = deflateSync(raw, { level: 6, memLevel: 8 });
      screened.push({ form, raw, score: z.length + formOverhead(form) });
    }
  }
  screened.sort((a, b) => a.score - b.score);
  const bestForm = screened[0].form;
  // Band-wise filter search on the winning form.
  const bandRaw = bandSearchRaw(bestForm.samples, w, h, bestForm.bpp, 90);
  const bandZ = deflateSync(bandRaw, { level: 6, memLevel: 8 });
  screened.push({ form: bestForm, raw: bandRaw, score: bandZ.length + formOverhead(bestForm) });
  screened.sort((a, b) => a.score - b.score);
  // Stage 2: final zlib settings on the best few distinct raws.
  const finalists = [];
  const seenRaw = new Set();
  for (const entry of screened) {
    if (seenRaw.has(entry.raw)) continue;
    seenRaw.add(entry.raw);
    finalists.push(entry);
    if (finalists.length >= 2) break;
  }
  let bestPng = null;
  let bestRawEntry = null;
  let bestZlibSize = Infinity;
  for (const entry of finalists) {
    const z = deflateSync(entry.raw, { level: 9, memLevel: 8, strategy: constants.Z_DEFAULT_STRATEGY });
    const png = assemblePng(w, h, entry.form, new Uint8Array(z.buffer, z.byteOffset, z.length));
    if (bestPng === null || png.length < bestPng.length) {
      bestPng = png;
      bestRawEntry = entry;
      bestZlibSize = png.length;
    }
  }
  if (bestRawEntry) {
    const z = deflateSync(bestRawEntry.raw, { level: 9, memLevel: 9, strategy: constants.Z_FILTERED });
    const png = assemblePng(w, h, bestRawEntry.form, new Uint8Array(z.buffer, z.byteOffset, z.length));
    if (png.length < bestPng.length) {
      bestPng = png;
      bestZlibSize = png.length;
    }
  }
  // Optimal-parsing deflate on the winning raw when the prize is worth the work.
  if (bestRawEntry && bestZlibSize > 40000) {
    try {
      const z = deflateOptimal(bestRawEntry.raw, 3, 64);
      const png = assemblePng(w, h, bestRawEntry.form, z);
      if (png.length < bestPng.length) bestPng = png;
    } catch {
      // Keep the zlib winner; a failed refinement must never lose the instance.
    }
  }
  return bestPng;
}

function main() {
  const ids = readdirSync(IN_DIR).sort();
  for (const id of ids) {
    const inPath = join(IN_DIR, id, 'image.png');
    let isFile = false;
    try {
      isFile = statSync(inPath).isFile();
    } catch {
      isFile = false;
    }
    if (!isFile) continue;
    mkdirSync(join(OUT_DIR, id), { recursive: true });
    const outPath = join(OUT_DIR, id, 'image.png');
    try {
      const bytes = new Uint8Array(readFileSync(inPath));
      const img = decodePng(bytes);
      const squeezed = squeezeImage(img.rgba, img.w, img.h);
      writeFileSync(outPath, squeezed);
    } catch {
      copyFileSync(inPath, outPath);
    }
  }
}
main();
