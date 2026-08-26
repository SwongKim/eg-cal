/* Eg-Cal : 공학용 연산 도우미 — 메인 애플리케이션
   Claude Design 프로토타입(공학용 연산 도우미.dc.html)의 통계/계산 로직을 그대로 이식하고,
   화면은 실제 React 컴포넌트로, 인증은 Firebase Authentication(firebase-config.js)으로 구현. */

const { useState, useEffect, useRef, useCallback, useMemo } = React;

/* ============================================================
   1. 숫자 · 통계 분포 헬퍼
   ============================================================ */
function fmt(v, d = 4) {
  if (v === null || v === undefined || typeof v !== "number" || !isFinite(v)) return "—";
  const a = Math.abs(v);
  if (a !== 0 && (a < 1e-4 || a >= 1e6)) return v.toExponential(2);
  return v.toFixed(d);
}
function fmtP(p) {
  if (p === null || p === undefined || !isFinite(p)) return "—";
  if (p < 0.0001) return "<0.0001";
  return p.toFixed(4);
}
function gammaln(x) {
  const c = [76.18009172947146, -86.50532032941677, 24.01409824083091, -1.231739572450155, 0.1208650973866179e-2, -0.5395239384953e-5];
  let y = x, tmp = x + 5.5; tmp -= (x + 0.5) * Math.log(tmp);
  let ser = 1.000000000190015;
  for (let j = 0; j < 6; j++) ser += c[j] / ++y;
  return -tmp + Math.log(2.5066282746310005 * ser / x);
}
function betacf(a, b, x) {
  const qab = a + b, qap = a + 1, qam = a - 1;
  let c = 1, d = 1 - qab * x / qap;
  if (Math.abs(d) < 1e-30) d = 1e-30;
  d = 1 / d; let h = d;
  for (let m = 1; m <= 200; m++) {
    const m2 = 2 * m;
    let aa = m * (b - m) * x / ((qam + m2) * (a + m2));
    d = 1 + aa * d; if (Math.abs(d) < 1e-30) d = 1e-30;
    c = 1 + aa / c; if (Math.abs(c) < 1e-30) c = 1e-30;
    d = 1 / d; h *= d * c;
    aa = -(a + m) * (qab + m) * x / ((a + m2) * (qap + m2));
    d = 1 + aa * d; if (Math.abs(d) < 1e-30) d = 1e-30;
    c = 1 + aa / c; if (Math.abs(c) < 1e-30) c = 1e-30;
    d = 1 / d;
    const del = d * c; h *= del;
    if (Math.abs(del - 1) < 3e-8) break;
  }
  return h;
}
function betai(a, b, x) {
  if (!isFinite(x) || x <= 0) return 0;
  if (x >= 1) return 1;
  const bt = Math.exp(gammaln(a + b) - gammaln(a) - gammaln(b) + a * Math.log(x) + b * Math.log(1 - x));
  return x < (a + 1) / (a + b + 2) ? bt * betacf(a, b, x) / a : 1 - bt * betacf(b, a, 1 - x) / b;
}
function pT(t, df) { if (!isFinite(t) || df <= 0) return NaN; return betai(df / 2, 0.5, df / (df + t * t)); }
function pF(F, d1, d2) { if (!isFinite(F) || F <= 0 || d1 <= 0 || d2 <= 0) return NaN; return betai(d2 / 2, d1 / 2, d2 / (d2 + d1 * F)); }
const T_TABLE = {1:12.706,2:4.303,3:3.182,4:2.776,5:2.571,6:2.447,7:2.365,8:2.306,9:2.262,10:2.228,
  11:2.201,12:2.179,13:2.160,14:2.145,15:2.131,16:2.120,17:2.110,18:2.101,19:2.093,20:2.086,
  21:2.080,22:2.074,23:2.069,24:2.064,25:2.060,26:2.056,27:2.052,28:2.048,29:2.045,30:2.042};
function tcrit(df) {
  if (df < 1) return NaN;
  if (T_TABLE[df]) return T_TABLE[df];
  if (df <= 40) return 2.021; if (df <= 60) return 2.000; if (df <= 120) return 1.980; return 1.960;
}
function qnorm(p) {
  const a=[-3.969683028665376e1,2.209460984245205e2,-2.759285104469687e2,1.383577518672690e2,-3.066479806614716e1,2.506628277459239],
        b=[-5.447609879822406e1,1.615858368580409e2,-1.556989798598866e2,6.680131188771972e1,-1.328068155288572e1],
        c=[-7.784894002430293e-3,-3.223964580411365e-1,-2.400758277161838,-2.549732539343734,4.374664141464968,2.938163982698783],
        d=[7.784695709041462e-3,3.224671290700398e-1,2.445134137142996,3.754408661907416];
  const pl = 0.02425; let q, r;
  if (p < pl) { q = Math.sqrt(-2 * Math.log(p)); return (((((c[0]*q+c[1])*q+c[2])*q+c[3])*q+c[4])*q+c[5]) / ((((d[0]*q+d[1])*q+d[2])*q+d[3])*q+1); }
  if (p <= 1 - pl) { q = p - 0.5; r = q * q; return (((((a[0]*r+a[1])*r+a[2])*r+a[3])*r+a[4])*r+a[5])*q / (((((b[0]*r+b[1])*r+b[2])*r+b[3])*r+b[4])*r+1); }
  q = Math.sqrt(-2 * Math.log(1 - p));
  return -(((((c[0]*q+c[1])*q+c[2])*q+c[3])*q+c[4])*q+c[5]) / ((((d[0]*q+d[1])*q+d[2])*q+d[3])*q+1);
}
function phi(z) {
  const t = 1 / (1 + 0.2316419 * Math.abs(z));
  const d = 0.3989423 * Math.exp(-z * z / 2);
  const p = d * t * (0.3193815 + t * (-0.3565638 + t * (1.781478 + t * (-1.821256 + t * 1.330274))));
  return z >= 0 ? 1 - p : p;
}

/* ============================================================
   2. 공학용 계산기 — 수식 파서
   ============================================================ */
function trimNum(v) {
  const a = Math.abs(v);
  if (a !== 0 && (a < 1e-9 || a >= 1e12)) return v.toExponential(6);
  return String(parseFloat(v.toPrecision(12)));
}
function parseExpr(src, deg) {
  const s = src.replace(/×/g, "*").replace(/÷/g, "/").replace(/−/g, "-").replace(/π/g, "PI").replace(/√/g, "sqrt");
  let i = 0;
  const ws = () => { while (i < s.length && s[i] === " ") i++; };
  function expr() { let v = term(); ws(); while (s[i] === "+" || s[i] === "-") { const o = s[i++]; const r = term(); v = o === "+" ? v + r : v - r; ws(); } return v; }
  function term() { let v = unary(); ws(); while (s[i] === "*" || s[i] === "/") { const o = s[i++]; const r = unary(); v = o === "*" ? v * r : v / r; ws(); } return v; }
  function unary() { ws(); if (s[i] === "-") { i++; return -unary(); } if (s[i] === "+") { i++; return unary(); } return power(); }
  function power() { const base = postfix(); ws(); if (s[i] === "^") { i++; return Math.pow(base, unary()); } return base; }
  function postfix() { let v = primary(); ws(); while (s[i] === "!") { i++; v = fact(v); ws(); } return v; }
  function fact(n) { if (n < 0 || n !== Math.floor(n) || n > 170) throw new Error("fact"); let r = 1; for (let k = 2; k <= n; k++) r *= k; return r; }
  function primary() {
    ws();
    if (s[i] === "(") { i++; const v = expr(); ws(); if (s[i] === ")") i++; return v; }
    const num = /^[0-9]*\.?[0-9]+(e[+-]?[0-9]+)?/i.exec(s.slice(i));
    if (num) { i += num[0].length; return parseFloat(num[0]); }
    const name = /^[A-Za-z]+/.exec(s.slice(i));
    if (name) {
      const id = name[0]; i += id.length;
      if (id === "PI") return Math.PI;
      if (id === "E" || id === "e") return Math.E;
      ws();
      let arg;
      if (s[i] === "(") { i++; arg = expr(); ws(); if (s[i] === ")") i++; } else arg = unary();
      const D = deg ? Math.PI / 180 : 1;
      switch (id) {
        case "sin": return Math.sin(arg * D);
        case "cos": return Math.cos(arg * D);
        case "tan": return Math.tan(arg * D);
        case "ln": return Math.log(arg);
        case "log": return Math.log10(arg);
        case "sqrt": return Math.sqrt(arg);
        case "exp": return Math.exp(arg);
        default: throw new Error("fn");
      }
    }
    throw new Error("parse");
  }
  const out = expr(); ws();
  if (i < s.length) throw new Error("trail");
  return out;
}

/* ============================================================
   3. 데이터 테이블 — 붙여넣기 파싱
   ============================================================ */
function parsePasteBlock(text) {
  const lines = text.replace(/\r/g, "").split("\n").filter((l) => l.trim() !== "");
  return lines.map((l) => l.split(/\t|,|\s{1,}/).filter((c) => c !== ""));
}
function sampleRows() {
  return [["0.5","0.412"],["0.5","0.398"],["0.5","0.421"],
    ["1","0.812"],["1","0.795"],["1","0.828"],
    ["2","1.601"],["2","1.632"],["2","1.588"],
    ["5","4.02"],["5","3.96"],["5","4.05"],
    ["10","7.94"],["10","8.06"],["10","7.98"]].map((r) => ({ x: r[0], y: r[1] }));
}

/* ============================================================
   4. 회귀분석 · 통계검정 엔진
   ============================================================ */
function runRegression(rows) {
  const pts = []; let bad = 0;
  rows.forEach((r) => {
    const sx = String(r.x).trim(), sy = String(r.y).trim();
    if (sx === "" && sy === "") return;
    const x = parseFloat(sx), y = parseFloat(sy);
    if (!isFinite(x) || !isFinite(y)) { bad++; return; }
    pts.push({ x, y });
  });
  if (pts.length < 3) {
    return { result: null, tableWarn: bad ? bad + "개 셀 오류" : "", emptyMsg: "유효한 데이터가 3행 이상 필요합니다. 현재 " + pts.length + "행." };
  }
  const n = pts.length;
  const xs = pts.map((p) => p.x), ys = pts.map((p) => p.y);
  const mx = xs.reduce((a, b) => a + b, 0) / n, my = ys.reduce((a, b) => a + b, 0) / n;
  let Sxx = 0, Syy = 0, Sxy = 0;
  pts.forEach((p) => { Sxx += (p.x - mx) ** 2; Syy += (p.y - my) ** 2; Sxy += (p.x - mx) * (p.y - my); });
  const b = Sxy / Sxx, a = my - b * mx;
  const fitted = pts.map((p) => a + b * p.x);
  const res = pts.map((p, i) => p.y - fitted[i]);
  const SSE = res.reduce((s, e) => s + e * e, 0), SSR = Syy - SSE, SST = Syy;
  const dfRes = n - 2;
  const MSE = SSE / dfRes, Syx = Math.sqrt(MSE);
  const R2 = SSR / SST, adjR2 = 1 - (1 - R2) * (n - 1) / dfRes;
  const r = Sxy / Math.sqrt(Sxx * Syy);
  const seB = Syx / Math.sqrt(Sxx), seA = Syx * Math.sqrt(1 / n + mx * mx / Sxx);
  const tB = b / seB, pB = pT(tB, dfRes);
  const F = (SSR / 1) / MSE, pFv = pF(F, 1, dfRes);
  const tc = tcrit(dfRes);
  const LOD = 3.3 * Syx / Math.abs(b), LOQ = 10 * Syx / Math.abs(b);

  const recs = [];
  pts.forEach((p) => { if (p.x !== 0) recs.push(((p.y - a) / b) / p.x * 100); });
  const recovery = recs.length ? recs.reduce((s, v) => s + v, 0) / recs.length : NaN;

  const gm = new Map();
  pts.forEach((p) => { const k = String(p.x); if (!gm.has(k)) gm.set(k, []); gm.get(k).push(p.y); });
  const groups = Array.from(gm.entries()).map(([k, v]) => ({ x: parseFloat(k), ys: v })).sort((p, q) => p.x - q.x);
  const rsds = [];
  groups.forEach((g) => {
    if (g.ys.length < 2) return;
    const m = g.ys.reduce((s, v) => s + v, 0) / g.ys.length;
    const sd = Math.sqrt(g.ys.reduce((s, v) => s + (v - m) ** 2, 0) / (g.ys.length - 1));
    if (m !== 0) rsds.push(Math.abs(sd / m) * 100);
  });
  const rsd = rsds.length ? rsds.reduce((s, v) => s + v, 0) / rsds.length : NaN;

  let lof = null;
  const reps = groups.filter((g) => g.ys.length > 1);
  if (reps.length >= 1 && groups.length > 2) {
    let SSPE = 0, dfPE = 0;
    groups.forEach((g) => {
      const m = g.ys.reduce((s, v) => s + v, 0) / g.ys.length;
      g.ys.forEach((v) => { SSPE += (v - m) ** 2; });
      dfPE += g.ys.length - 1;
    });
    const dfLF = groups.length - 2, SSLF = SSE - SSPE;
    if (dfPE > 0 && dfLF > 0) {
      const Fl = (SSLF / dfLF) / (SSPE / dfPE);
      lof = { F: Fl, p: pF(Fl, dfLF, dfPE), df: dfLF + ", " + dfPE };
    }
  }

  let lev = null;
  const lreps = groups.filter((g) => g.ys.length > 2);
  if (lreps.length >= 2) {
    const zs = lreps.map((g) => {
      const m = g.ys.reduce((s, v) => s + v, 0) / g.ys.length;
      return g.ys.map((v) => Math.abs(v - m));
    });
    const N = zs.reduce((s, z) => s + z.length, 0), k = zs.length;
    const zbar = zs.flat().reduce((s, v) => s + v, 0) / N;
    let num = 0, den = 0;
    zs.forEach((z) => {
      const zi = z.reduce((s, v) => s + v, 0) / z.length;
      num += z.length * (zi - zbar) ** 2;
      z.forEach((v) => { den += (v - zi) ** 2; });
    });
    const scale = Math.max(1e-12, Math.abs(zbar) * 1e-6);
    if (den > scale && N > k) {
      const W = (N - k) / (k - 1) * num / den;
      lev = { W, p: pF(W, k - 1, N - k), df: (k - 1) + ", " + (N - k) };
    }
  }

  const sr = res.slice().sort((p, q) => p - q);
  const mi = sr.map((_, i) => qnorm((i + 1 - 0.375) / (n + 0.25)));
  const mm = mi.reduce((s, v) => s + v, 0) / n, rm = sr.reduce((s, v) => s + v, 0) / n;
  let cnum = 0, cd1 = 0, cd2 = 0;
  sr.forEach((v, i) => { cnum += (v - rm) * (mi[i] - mm); cd1 += (v - rm) ** 2; cd2 += (mi[i] - mm) ** 2; });
  const Wsf = (cnum / Math.sqrt(cd1 * cd2)) ** 2;
  let pSF = NaN;
  if (n >= 5 && Wsf < 1) {
    const u = Math.log(n), v2 = Math.log(u);
    const mu = -1.2725 + 1.0521 * (v2 - u), sig2 = 1.0308 - 0.26758 * (v2 + 2 / u);
    pSF = 1 - phi((Math.log(1 - Wsf) - mu) / sig2);
  }

  const sdR = Math.sqrt(res.reduce((s, e) => s + (e - 0) ** 2, 0) / (n - 1));
  const G = Math.max.apply(null, res.map((e) => Math.abs(e))) / sdR;
  let pG = NaN;
  const uu = G * Math.sqrt(n) / (n - 1);
  if (uu < 1) { const t2 = uu * uu * (n - 2) / (1 - uu * uu); pG = Math.min(1, n * pT(Math.sqrt(t2), n - 2)); }

  const cook = pts.map((p, i) => {
    const h = 1 / n + (p.x - mx) ** 2 / Sxx;
    return (res[i] ** 2 / (2 * MSE)) * h / (1 - h) ** 2;
  });
  const cookMax = Math.max.apply(null, cook);

  let dwNum = 0;
  for (let i = 1; i < n; i++) dwNum += (res[i] - res[i - 1]) ** 2;
  const DW = SSE > 0 ? dwNum / SSE : NaN;
  const tA = a / seA, pA = pT(tA, dfRes);
  const tR = r * Math.sqrt(dfRes) / Math.sqrt(Math.max(1e-15, 1 - r * r)), pR = pT(tR, dfRes);
  const logOk = Math.min.apply(null, xs) > 0;

  const R = { n, a, b, r, R2, adjR2, Syx, seA, seB, tB, pB, F, pF: pFv, tc, LOD, LOQ, recovery, rsd,
    SSR, SSE, SST, dfRes, MSE, lof, lev, Wsf, pSF, G, pG, cookMax, DW, tA, pA, tR, pR, logOk,
    pts, res, fitted, groups, mx, Sxx };
  return { result: R, tableWarn: bad ? bad + "개 셀은 계산에서 제외" : "", emptyMsg: "" };
}

/* ============================================================
   5. 차트 좌표 계산 (SVG)
   ============================================================ */
function ticks(min, max) { const out = []; for (let i = 0; i <= 4; i++) out.push(min + (max - min) * i / 4); return out; }
function tlabel(v, span) {
  const a = Math.abs(v);
  if (a !== 0 && (a < 0.01 || a >= 10000)) return v.toExponential(1);
  if (span >= 50) return v.toFixed(0);
  if (span >= 5) return v.toFixed(1);
  if (span >= 0.5) return v.toFixed(2);
  return v.toFixed(3);
}
function makeAxis(min, max, p0, p1, flip) {
  const pad = (max - min) * 0.08 || (Math.abs(max) * 0.1 || 1);
  const lo = min - pad, hi = max + pad, span = hi - lo;
  const sc = (v) => flip ? p1 - (v - lo) / span * (p1 - p0) : p0 + (v - lo) / span * (p1 - p0);
  return { lo, hi, span, sc };
}
function yTicksOf(A) { return ticks(A.lo, A.hi).map((v) => ({ y: A.sc(v), ty: A.sc(v) + 3.5, label: tlabel(v, A.span) })); }
function sig(v) {
  const a = Math.abs(v);
  if (a === 0) return "0";
  if (a < 0.001 || a >= 10000) return v.toExponential(1);
  return String(parseFloat(v.toPrecision(3)));
}
function buildCharts(R, logX, logY) {
  const L = 52, Rr = 544, T = 14, B = 280;
  const xs = R.pts.map((p) => p.x), ys = R.pts.map((p) => p.y);
  const bands = true;
  const lg = !!logX && Math.min.apply(null, xs) > 0;
  const tX = (v) => lg ? Math.log10(v) : v;
  const iX = (t) => lg ? Math.pow(10, t) : t;

  const AX = makeAxis(tX(Math.min.apply(null, xs)), tX(Math.max.apply(null, xs)), L, Rr, false);
  const grid = [];
  for (let i = 0; i <= 60; i++) { const g = AX.lo + AX.span * i / 60; grid.push({ g, x: iX(g) }); }
  const band = (m) => grid.map((o) => ({ g: o.g, y: R.a + R.b * o.x, w: R.tc * R.Syx * Math.sqrt(m + 1 / R.n + (o.x - R.mx) ** 2 / R.Sxx) }));
  const ci = band(0), pi = band(1);
  const yAll = ys.concat(bands ? pi.map((p) => p.y + p.w).concat(pi.map((p) => p.y - p.w)) : grid.map((o) => R.a + R.b * o.x));
  const AY = makeAxis(Math.min.apply(null, yAll), Math.max.apply(null, yAll), T, B, true);
  const bandPath = (arr) => "M" + arr.map((p) => AX.sc(p.g).toFixed(1) + " " + AY.sc(p.y + p.w).toFixed(1)).join(" L") +
    " L" + arr.slice().reverse().map((p) => AX.sc(p.g).toFixed(1) + " " + AY.sc(p.y - p.w).toFixed(1)).join(" L") + " Z";
  const xt = ticks(AX.lo, AX.hi).map((v) => ({ x: +AX.sc(v).toFixed(1), label: lg ? sig(iX(v)) : tlabel(v, AX.span) }));
  const fit = {
    pts: R.pts.map((p) => ({ cx: +AX.sc(tX(p.x)).toFixed(1), cy: +AY.sc(p.y).toFixed(1) })),
    line: "M" + grid.map((o) => AX.sc(o.g).toFixed(1) + " " + AY.sc(R.a + R.b * o.x).toFixed(1)).join(" L"),
    ci: bandPath(ci), pi: bandPath(pi),
    xt, yt: yTicksOf(AY),
  };

  const rmax = Math.max.apply(null, R.res.map((e) => Math.abs(e))) || 1;
  const RY = makeAxis(-rmax, rmax, T, B, true);
  const resid = {
    pts: R.pts.map((p, i) => ({ cx: +AX.sc(tX(p.x)).toFixed(1), cy: +RY.sc(R.res[i]).toFixed(1) })),
    zero: +RY.sc(0).toFixed(1), xt, yt: yTicksOf(RY),
  };

  const G = R.groups, k = G.length;
  const slot = (Rr - L) / k;

  // 구간 그림에 필요한 수준별 평균 · 95% CI 반폭 (원 단위, 로그 변환 전에 먼저 계산 — 신뢰구간은 항상 선형 값으로 계산하고, 축 표시만 로그로 바꾼다)
  const ig = G.map((g, i) => {
    const cx = L + slot * (i + 0.5);
    const m = g.ys.reduce((s, v) => s + v, 0) / g.ys.length;
    let hw = 0;
    if (g.ys.length > 1) {
      const sd = Math.sqrt(g.ys.reduce((s, v) => s + (v - m) ** 2, 0) / (g.ys.length - 1));
      hw = tcrit(g.ys.length - 1) * sd / Math.sqrt(g.ys.length);
    }
    return { m, hw, cx };
  });
  // Y 로그 전환 가능 여부: 관측값이 모두 양수이고, 구간 그림의 95% 하한도 0보다 커야 함
  const catLogOk = Math.min.apply(null, ys) > 0 && ig.every((o) => o.m - o.hw > 0);
  const lgY = !!logY && catLogOk;
  const tY = (v) => lgY ? Math.log10(v) : v;
  const iY = (t) => lgY ? Math.pow(10, t) : t;
  const yTicksLog = (A) => ticks(A.lo, A.hi).map((v) => ({ y: A.sc(v), ty: A.sc(v) + 3.5, label: lgY ? sig(iY(v)) : tlabel(v, A.span) }));

  const GY = makeAxis(tY(Math.min.apply(null, ys)), tY(Math.max.apply(null, ys)), T, B, true);
  const q = (arr, p) => {
    const s = arr.slice().sort((x, y) => x - y);
    const h = (s.length - 1) * p, lo = Math.floor(h), hi = Math.ceil(h);
    return s[lo] + (s[hi] - s[lo]) * (h - lo);
  };
  const box = { yt: yTicksLog(GY), groups: G.map((g, i) => {
    const cx = L + slot * (i + 0.5), bw = Math.min(52, slot * 0.5);
    const q1 = q(g.ys, 0.25), q3 = q(g.ys, 0.75), med = q(g.ys, 0.5);
    const iqr = q3 - q1;
    const lo = Math.max(Math.min.apply(null, g.ys), q1 - 1.5 * iqr), hi = Math.min(Math.max.apply(null, g.ys), q3 + 1.5 * iqr);
    const rawH = GY.sc(tY(q1)) - GY.sc(tY(q3));
    const bh = Math.max(8, rawH), top = GY.sc(tY(q3)) - (bh - rawH) / 2;
    const cLo = Math.max(GY.sc(tY(lo)), top + bh + 4), cHi = Math.min(GY.sc(tY(hi)), top - 4);
    return { cx: +cx.toFixed(1), bx: +(cx - bw / 2).toFixed(1), br: +(cx + bw / 2).toFixed(1), bw: +bw.toFixed(1),
      wl: +(cx - bw / 2.6).toFixed(1), wr: +(cx + bw / 2.6).toFixed(1),
      q3: +top.toFixed(1), bh: +bh.toFixed(1),
      med: +Math.min(top + bh - 1, Math.max(top + 1, GY.sc(tY(med)))).toFixed(1),
      lo: +cLo.toFixed(1), hi: +cHi.toFixed(1),
      label: tlabel(g.x, Math.max.apply(null, xs) - Math.min.apply(null, xs)) };
  }) };
  const dots = [];
  G.forEach((g, i) => {
    const cx = L + slot * (i + 0.5);
    g.ys.forEach((v, j) => dots.push({ cx: +(cx + (j - (g.ys.length - 1) / 2) * 9).toFixed(1), cy: +GY.sc(tY(v)).toFixed(1) }));
  });
  const ind = { yt: yTicksLog(GY), dots, groups: G.map((g, i) => {
    const cx = L + slot * (i + 0.5), m = g.ys.reduce((s, v) => s + v, 0) / g.ys.length;
    return { cx: +cx.toFixed(1), wl: +(cx - 16).toFixed(1), wr: +(cx + 16).toFixed(1), mean: +GY.sc(tY(m)).toFixed(1), label: box.groups[i].label };
  }) };
  const iAllT = ig.map((o) => tY(o.m + o.hw)).concat(ig.map((o) => tY(o.m - o.hw)));
  const IY = makeAxis(Math.min.apply(null, iAllT), Math.max.apply(null, iAllT), T, B, true);
  const intv = { yt: yTicksLog(IY), groups: ig.map((o, i) => ({
    cx: +o.cx.toFixed(1), wl: +(o.cx - 11).toFixed(1), wr: +(o.cx + 11).toFixed(1),
    mean: +IY.sc(tY(o.m)).toFixed(1), hi: +IY.sc(tY(o.m + o.hw)).toFixed(1), lo: +IY.sc(tY(o.m - o.hw)).toFixed(1),
    label: box.groups[i].label })), stats: ig.map((o, i) => ({ x: G[i].x, m: o.m, hw: o.hw })) };

  return { fit, resid, box, ind, intv, catLogOk };
}

/* ============================================================
   5b. 차트 해설 — 통계 결과를 바탕으로 자동 생성되는 분석 문구
   ============================================================ */
function captionFit(R, lgOn) {
  const strength = R.R2 >= 0.995 ? "매우 우수한 선형성" : R.R2 >= 0.98 ? "우수한 선형성" : R.R2 >= 0.9 ? "양호한 선형성" : "다소 낮은 선형성";
  let s = "R² = " + fmt(R.R2, 4) + "로 데이터 변동의 약 " + fmt(R.R2 * 100, 1) + "%가 회귀식으로 설명되며, " + strength + "을 보입니다. ";
  s += R.pF < 0.05 ? "회귀는 통계적으로 유의합니다 (p " + fmtP(R.pF) + ")." : "회귀가 통계적으로 유의하지 않습니다 (p " + fmtP(R.pF) + ") — 데이터를 다시 확인하세요.";
  if (lgOn) s += " X 축은 로그 스케일로 표시 중입니다.";
  return s;
}
function captionResid(R) {
  let s;
  if (R.lof) {
    s = R.lof.p < 0.05
      ? "적합결여 검정에서 유의한 결과가 나와(p " + fmtP(R.lof.p) + ") 선형 모형이 부적절할 가능성이 있습니다. 잔차에 곡선 형태의 경향이 있는지 확인하세요."
      : "적합결여 검정 결과 선형 모형이 적절합니다 (p " + fmtP(R.lof.p) + "). 잔차가 0을 중심으로 무작위로 흩어져 있습니다.";
  } else {
    s = "잔차가 점선(0) 주위에 뚜렷한 패턴 없이 흩어져 있으면 선형 모형이 적절하다고 볼 수 있습니다. (반복 측정 수준이 부족해 적합결여 검정은 생략됨)";
  }
  if (isFinite(R.DW)) s += R.DW > 1.5 && R.DW < 2.5 ? " Durbin-Watson 검정 상 잔차의 자기상관은 없습니다." : " Durbin-Watson 검정에서 잔차 자기상관 가능성이 있습니다 — 데이터 입력 순서를 확인하세요.";
  return s;
}
function captionBox(R) {
  if (R.lev) {
    return R.lev.p < 0.05
      ? "Levene 등분산성 검정에서 유의한 결과가 나와(p " + fmtP(R.lev.p) + ") 인자 수준별 분산이 다를 수 있습니다 (이분산). 가중회귀 적용을 고려해 보세요."
      : "Levene 등분산성 검정 결과 인자 수준 간 분산이 유사합니다 (p " + fmtP(R.lev.p) + ") — 등분산 가정이 유지됩니다.";
  }
  return "각 인자 수준의 반복 측정이 3회 미만이라 등분산성 검정은 생략되었습니다. 상자(사분위범위)의 크기가 인자에 따라 커지는지 육안으로 확인해 보세요.";
}
function captionInd(R) {
  if (!isFinite(R.rsd)) return "수준별 반복 측정이 2회 미만이라 %RSD를 산출할 수 없습니다.";
  const grade = R.rsd < 2 ? "매우 우수한" : R.rsd < 5 ? "우수한" : R.rsd < 10 ? "양호한" : "개선이 필요한";
  return "수준별 반복 측정값의 평균 %RSD = " + fmt(R.rsd, 2) + "% 로 " + grade + " 반복재현성을 보입니다. 각 인자에서 점들이 평균선(터콰이즈색)에 가까이 모여 있을수록 재현성이 좋다는 뜻입니다.";
}
function captionInt(stats) {
  if (stats.length < 2) return "비교할 인자 수준이 2개 미만입니다.";
  let overlap = 0;
  for (let i = 0; i < stats.length - 1; i++) {
    const a = stats[i], b = stats[i + 1];
    const aLo = a.m - a.hw, aHi = a.m + a.hw, bLo = b.m - b.hw, bHi = b.m + b.hw;
    if (Math.max(aLo, bLo) <= Math.min(aHi, bHi)) overlap++;
  }
  return overlap === 0
    ? "인접한 모든 인자 수준의 95% 신뢰구간이 서로 겹치지 않아, 수준 간 반응 차이가 뚜렷하게 구분됩니다."
    : "인접한 인자 수준 중 " + overlap + "쌍의 95% 신뢰구간이 겹칩니다 — 해당 수준들은 반응 차이가 통계적으로 뚜렷하지 않을 수 있습니다.";
}

/* ============================================================
   6. 복사 / PNG 내보내기
   ============================================================ */
function copyToClipboard(text, html, done) {
  try {
    if (html && navigator.clipboard && window.ClipboardItem) {
      navigator.clipboard.write([new ClipboardItem({
        "text/html": new Blob([html], { type: "text/html" }),
        "text/plain": new Blob([text], { type: "text/plain" }),
      })]).then(done, () => { navigator.clipboard.writeText(text).then(done, done); });
    } else if (navigator.clipboard) navigator.clipboard.writeText(text).then(done, done);
    else done();
  } catch (e) { done(); }
}
function tsv(rows) { return rows.map((r) => r.join("\t")).join("\n"); }
function htmlTable(rows) {
  return "<table border=\"1\" cellspacing=\"0\" cellpadding=\"4\">" + rows.map((r, i) =>
    "<tr>" + r.map((c) => (i === 0 ? "<th>" + c + "</th>" : "<td>" + c + "</td>")).join("") + "</tr>").join("") + "</table>";
}
function exportSvgAsPng(id, name) {
  const svg = document.getElementById(id);
  if (!svg) return;
  const s = new XMLSerializer().serializeToString(svg);
  const img = new Image();
  img.onload = () => {
    const c = document.createElement("canvas");
    c.width = 1120; c.height = 640;
    const ctx = c.getContext("2d");
    ctx.fillStyle = "#17233e"; ctx.fillRect(0, 0, c.width, c.height);
    ctx.drawImage(img, 0, 0, c.width, c.height);
    c.toBlob((bl) => {
      const u = URL.createObjectURL(bl);
      const link = document.createElement("a");
      link.href = u; link.download = name + ".png"; link.click();
      setTimeout(() => URL.revokeObjectURL(u), 2000);
    });
  };
  img.src = "data:image/svg+xml;charset=utf-8," + encodeURIComponent(s);
}

/* ============================================================
   7. Firebase 오류 메시지 한글화
   ============================================================ */
function authErrorMessage(err) {
  const code = err && err.code;
  const map = {
    "auth/invalid-email": "이메일 형식이 올바르지 않습니다.",
    "auth/user-not-found": "존재하지 않는 계정입니다.",
    "auth/wrong-password": "비밀번호가 일치하지 않습니다.",
    "auth/invalid-credential": "이메일 또는 비밀번호가 올바르지 않습니다.",
    "auth/email-already-in-use": "이미 가입된 이메일입니다.",
    "auth/weak-password": "비밀번호는 6자 이상이어야 합니다.",
    "auth/too-many-requests": "잠시 후 다시 시도해주세요.",
    "auth/network-request-failed": "네트워크 오류가 발생했습니다.",
    "auth/api-key-not-valid.-please-pass-a-valid-api-key.": "Firebase 설정이 아직 완료되지 않았습니다 (firebase-config.js 확인).",
  };
  if (map[code]) return map[code];
  if (!window.EgCalAuth || !window.EgCalAuth.isConfigured) return "Firebase 설정이 아직 완료되지 않았습니다 (firebase-config.js 확인).";
  return "오류가 발생했습니다. 잠시 후 다시 시도해주세요.";
}

/* ============================================================
   8. 라우터 — /login /signup /reset-password /app /* (Sitemap.md)
   ============================================================ */
function useRouter() {
  const [path, setPath] = useState(window.location.pathname);
  useEffect(() => {
    const onPop = () => setPath(window.location.pathname);
    window.addEventListener("popstate", onPop);
    return () => window.removeEventListener("popstate", onPop);
  }, []);
  const navigate = useCallback((to) => {
    if (to !== window.location.pathname) window.history.pushState({}, "", to);
    setPath(to);
  }, []);
  return { path, navigate };
}

/* ============================================================
   9. 인증 상태 구독
   ============================================================ */
function useAuth() {
  const [ready, setReady] = useState(!!window.EgCalAuth);
  const [user, setUser] = useState(undefined);
  useEffect(() => {
    let unsub;
    const bind = () => { setReady(true); unsub = window.EgCalAuth.onAuthChange(setUser); };
    if (window.EgCalAuth) bind();
    else window.addEventListener("egcal-auth-ready", bind, { once: true });
    return () => { window.removeEventListener("egcal-auth-ready", bind); if (unsub) unsub(); };
  }, []);
  return { authLoading: !ready || user === undefined, user };
}

/* ============================================================
   10. 랜딩 페이지 (/)
   ============================================================ */
function LandingScreen({ navigate }) {
  const features = [
    { k: "공학용 계산기", v: "삼각함수 · 로그/지수 · 거듭제곱 · 메모리 등 표준 공학 연산을 마우스와 키보드로." },
    { k: "회귀분석 · 통계", v: "검량선 데이터를 입력하면 회귀식, LOD/LOQ, 신뢰구간, ANOVA, 그래프까지 한 번에 산출." },
    { k: "결과 기록 저장", v: "산출한 결과를 계정별로 저장해두고 필요할 때 다시 열람." },
  ];
  return (
    <div style={{ minHeight: "100vh", display: "flex", flexDirection: "column", justifyContent: "center", padding: "48px 28px", animation: "noct-in .28s ease" }}>
      <div style={{ width: "100%", maxWidth: 640, margin: "0 auto" }}>
        <div style={{ display: "flex", alignItems: "center", gap: 9, marginBottom: 34 }}>
          <Logo />
          <span style={{ fontSize: 15, fontWeight: 500, letterSpacing: "-.01em" }}>Eg-Cal : 공학용 연산 도우미</span>
        </div>
        <h1 style={{ fontSize: "clamp(28px,4vw,42px)", margin: "0 0 14px", maxWidth: "18ch" }}>계산과 통계 분석을 한 화면에서.</h1>
        <p style={{ fontSize: 14.5, color: "rgba(233,233,237,.6)", margin: "0 0 30px", maxWidth: "50ch", lineHeight: 1.6 }}>
          검량선 데이터를 입력하고 확인만 누르면 회귀식과 통계량, 그래프까지 바로 산출됩니다. 계산기와 분석 도구를 오가는 번거로움 없이 한 페이지에서 처리하세요.
        </p>
        <div style={{ display: "flex", gap: 10, flexWrap: "wrap", marginBottom: 44 }}>
          <button className="btn btn-primary" onClick={() => navigate("/login")} style={{ minHeight: 42, padding: "0 22px", fontSize: 14.5 }}>로그인</button>
          <button className="btn btn-secondary" onClick={() => navigate("/signup")} style={{ minHeight: 42, padding: "0 22px", fontSize: 14.5 }}>회원가입</button>
        </div>
        <div style={{ display: "grid", gridTemplateColumns: "repeat(auto-fit,minmax(160px,1fr))", gap: 14 }}>
          {features.map((f, i) => (
            <div key={i} style={{ background: "#17233e", borderRadius: 14, padding: "16px 17px", boxShadow: "0 0 0 1px #3f424d" }}>
              <div style={{ fontSize: 13.5, fontWeight: 500, marginBottom: 6 }}>{f.k}</div>
              <div style={{ fontSize: 12, color: "rgba(233,233,237,.55)", lineHeight: 1.55 }}>{f.v}</div>
            </div>
          ))}
        </div>
      </div>
    </div>
  );
}

/* ============================================================
   11. 로그인 / 회원가입 / 비밀번호 재설정 화면
   ============================================================ */
function AuthScreen({ mode, navigate }) {
  const [email, setEmail] = useState("");
  const [pw, setPw] = useState("");
  const [pw2, setPw2] = useState("");
  const [agree, setAgree] = useState(false);
  const [err, setErr] = useState({});
  const [notice, setNotice] = useState("");
  const [busy, setBusy] = useState(false);

  const titles = { login: "로그인", signup: "회원가입", reset: "비밀번호 재설정" };
  const subs = {
    login: "실험 데이터의 검량선과 통계 분석을 한 화면에서 처리합니다.",
    signup: "이메일과 비밀번호만으로 바로 시작할 수 있습니다.",
    reset: "가입한 이메일 주소로 재설정 링크를 보냅니다.",
  };
  const ctas = { login: "로그인", signup: "가입하기", reset: "재설정 메일 보내기" };

  async function submit() {
    const em = email.trim().toLowerCase();
    const okEmail = /^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(em);
    const e = {};
    if (!em) e.email = "이메일을 입력하세요.";
    else if (!okEmail) e.email = "이메일 형식이 올바르지 않습니다.";
    if (mode !== "reset") {
      if (!pw) e.pw = "비밀번호를 입력하세요.";
      else if (pw.length < 8) e.pw = "비밀번호는 8자 이상이어야 합니다.";
    }
    if (mode === "signup") {
      if (!pw2) e.pw2 = "비밀번호를 다시 입력하세요.";
      else if (pw !== pw2) e.pw2 = "비밀번호가 일치하지 않습니다.";
      if (!agree) e.agree = "개인정보 수집 및 이용에 동의해야 가입할 수 있습니다.";
    }
    if (Object.keys(e).length) { setErr(e); setNotice(""); return; }
    setErr({}); setBusy(true);
    try {
      if (mode === "login") await window.EgCalAuth.login(em, pw);
      else if (mode === "signup") { await window.EgCalAuth.signup(em, pw); }
      else { await window.EgCalAuth.resetPassword(em); setNotice(em + " 로 재설정 메일을 보냈습니다. 메일함을 확인하세요."); }
    } catch (ex) {
      setErr({ form: authErrorMessage(ex) });
    } finally {
      setBusy(false);
    }
  }

  const links = mode === "login"
    ? [{ pre: "계정이 없으신가요?", label: "회원가입", to: "/signup" }, { pre: "", label: "비밀번호를 잊으셨나요?", to: "/reset-password" }]
    : [{ pre: "이미 계정이 있으신가요?", label: "로그인", to: "/login" }];

  return (
    <div style={{ minHeight: "100vh", display: "flex", flexDirection: "column", justifyContent: "center", padding: "48px 28px", animation: "noct-in .28s ease" }}>
      <div style={{ width: "100%", maxWidth: 392, margin: "0 auto" }}>
        <div style={{ display: "flex", alignItems: "center", gap: 9, marginBottom: 34 }}>
          <Logo />
          <span style={{ fontSize: 15, fontWeight: 500, letterSpacing: "-.01em" }}>Eg-Cal : 공학용 연산 도우미</span>
        </div>
        <h2 style={{ fontSize: 29, margin: "0 0 8px" }}>{titles[mode]}</h2>
        <p style={{ fontSize: 13.5, color: "rgba(233,233,237,.55)", margin: "0 0 26px", maxWidth: "34ch" }}>{subs[mode]}</p>

        <div style={{ display: "flex", flexDirection: "column", gap: 14 }}>
          <div className="field">
            <label>이메일</label>
            <input className="input" type="email" value={email} onChange={(e) => setEmail(e.target.value)}
              onKeyDown={(e) => e.key === "Enter" && submit()} placeholder="you@lab.ac.kr"
              style={{ minHeight: 40, borderColor: err.email ? "#abfcf7" : undefined }} />
            {err.email && <FieldError text={err.email} />}
          </div>

          {mode !== "reset" && (
            <div className="field">
              <label>비밀번호</label>
              <input className="input" type="password" value={pw} onChange={(e) => setPw(e.target.value)}
                onKeyDown={(e) => e.key === "Enter" && submit()} placeholder="8자 이상"
                style={{ minHeight: 40, borderColor: err.pw ? "#abfcf7" : undefined }} />
              {err.pw && <FieldError text={err.pw} />}
            </div>
          )}

          {mode === "signup" && (
            <div className="field">
              <label>비밀번호 확인</label>
              <input className="input" type="password" value={pw2} onChange={(e) => setPw2(e.target.value)}
                onKeyDown={(e) => e.key === "Enter" && submit()}
                style={{ minHeight: 40, borderColor: err.pw2 ? "#abfcf7" : undefined }} />
              {err.pw2 && <FieldError text={err.pw2} />}
            </div>
          )}

          {mode === "signup" && (
            <div style={{ padding: "12px 13px", borderRadius: 8, background: "#141d34", border: "1px solid " + (err.agree ? "#abfcf7" : "rgba(233,233,237,.28)") }}>
              <label style={{ display: "flex", alignItems: "flex-start", gap: 9, cursor: "pointer" }}>
                <input type="checkbox" checked={agree} onChange={(e) => { setAgree(e.target.checked); setErr((p) => ({ ...p, agree: undefined })); }}
                  style={{ width: 16, height: 16, marginTop: 2, flex: "none", accentColor: "#84d9d3", cursor: "pointer" }} />
                <span style={{ fontSize: 12.5, lineHeight: 1.5, color: "rgba(233,233,237,.75)" }}>
                  개인정보 수집 및 이용 동의 <span style={{ color: "#abfcf7" }}>(필수)</span><br />
                  <span style={{ fontSize: 11.5, color: "rgba(233,233,237,.45)" }}>수집 항목: 이메일 주소 · 이용 목적: 계정 식별 및 서비스 제공 · 보유 기간: 회원 탈퇴 시까지</span>
                </span>
              </label>
              {err.agree && <FieldError text={err.agree} />}
            </div>
          )}

          {err.form && <div style={{ padding: "11px 13px", borderRadius: 8, background: "#3a6a67", border: "1px solid rgba(171,252,247,.35)", fontSize: 12.5, color: "#f4fffe" }}>{err.form}</div>}
          {notice && <div style={{ padding: "11px 13px", borderRadius: 8, background: "#27413f", border: "1px solid rgba(171,252,247,.35)", fontSize: 12.5, color: "#cefdfa" }}>{notice}</div>}

          <button className="btn btn-primary btn-block" disabled={busy} onClick={submit} style={{ minHeight: 42, fontSize: 14.5, marginTop: 4 }}>
            {busy ? "처리 중…" : ctas[mode]}
          </button>
        </div>

        <div style={{ height: 1, margin: "26px 0 18px", background: "linear-gradient(to right,transparent,rgba(233,233,237,.14) 40px,rgba(233,233,237,.14) calc(100% - 40px),transparent)" }} />
        <div style={{ display: "flex", flexWrap: "wrap", gap: "6px 18px", fontSize: 12.5, color: "rgba(233,233,237,.5)" }}>
          {links.map((l, i) => (
            <span key={i} style={{ display: "flex", gap: 6, alignItems: "baseline" }}>
              {l.pre}
              <button className="btn btn-ghost" onClick={() => navigate(l.to)} style={{ fontSize: 12.5, padding: 0 }}>{l.label}</button>
            </span>
          ))}
        </div>
        {!window.EgCalAuth?.isConfigured && (
          <p style={{ marginTop: 18, fontSize: 11.5, color: "rgba(233,233,237,.4)" }}>
            ⚠ firebase-config.js 에 Firebase 프로젝트 설정을 입력해야 로그인이 동작합니다.
          </p>
        )}
      </div>
    </div>
  );
}
function FieldError({ text }) {
  return <div style={{ fontSize: 11.5, color: "#cefdfa", marginTop: 5, display: "flex", gap: 5, alignItems: "center" }}>
    <span style={{ width: 3, height: 11, background: "#abfcf7", borderRadius: 2 }} />{text}
  </div>;
}
function Logo() {
  return <svg width="22" height="22" viewBox="0 0 22 22" fill="none" stroke="#84d9d3" strokeWidth="1.6">
    <path d="M3 18 C7 18 8 4 12 4 C16 4 17 11 19 11" strokeLinecap="round" />
    <circle cx="6.5" cy="16" r="1.6" fill="#84d9d3" stroke="none" />
    <circle cx="15.5" cy="8" r="1.6" fill="#84d9d3" stroke="none" />
  </svg>;
}

/* ============================================================
   12. 계산기
   ============================================================ */
function Calculator() {
  const [expr, setExpr] = useState("");
  const [out, setOut] = useState("0");
  const [err, setErr] = useState(false);
  const [mem, setMem] = useState(0);
  const [deg, setDeg] = useState(true);

  const push = useCallback((s) => setExpr((e) => e + s), []);
  const back = useCallback(() => setExpr((e) => e.slice(0, -1)), []);
  const evaluate = useCallback(() => {
    setExpr((cur) => {
      const src = cur.trim();
      if (!src) return cur;
      try {
        const v = parseExpr(src, deg);
        if (!isFinite(v)) throw new Error("range");
        setOut(trimNum(v)); setErr(false);
      } catch (e) { setOut("오류"); setErr(true); }
      return cur;
    });
  }, [deg]);

  useEffect(() => {
    const onKey = (e) => {
      const t = e.target;
      if (t && (t.tagName === "INPUT" || t.tagName === "TEXTAREA")) return;
      const k = e.key;
      if (/^[0-9.]$/.test(k)) push(k);
      else if (["+", "-", "*", "/", "^", "(", ")"].includes(k)) push(k);
      else if (k === "Enter" || k === "=") evaluate();
      else if (k === "Backspace") back();
      else if (k === "Escape") { setExpr(""); setOut("0"); setErr(false); }
      else return;
      e.preventDefault();
    };
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, [push, back, evaluate]);

  function memOp(op) {
    if (op === "c") { setMem(0); return; }
    if (op === "r") { push(trimNum(mem)); return; }
    const cur = parseFloat(out);
    if (!isFinite(cur)) return;
    setMem((m) => (op === "+" ? m + cur : m - cur));
  }

  const numDefs = [
    ["C", () => { setExpr(""); setOut("0"); setErr(false); }, "util", "14px"],
    ["⌫", back, "util", "15px"], ["(", () => push("("), "op"], [")", () => push(")"), "op"],
    ["7", () => push("7"), "num"], ["8", () => push("8"), "num"], ["9", () => push("9"), "num"], ["÷", () => push("/"), "op", "17px"],
    ["4", () => push("4"), "num"], ["5", () => push("5"), "num"], ["6", () => push("6"), "num"], ["×", () => push("*"), "op", "17px"],
    ["1", () => push("1"), "num"], ["2", () => push("2"), "num"], ["3", () => push("3"), "num"], ["−", () => push("-"), "op", "17px"],
    ["0", () => push("0"), "num"], [".", () => push("."), "num"], ["±", () => push("-"), "util", "15px"], ["+", () => push("+"), "op", "17px"],
  ];
  const funcDefs = [
    ["sin", () => push("sin("), "op", "13px"], ["cos", () => push("cos("), "op", "13px"],
    ["tan", () => push("tan("), "op", "13px"], ["√", () => push("sqrt("), "op", "15px"],
    ["ln", () => push("ln("), "op", "13px"], ["log", () => push("log("), "op", "13px"],
    ["xʸ", () => push("^"), "op", "14px"], ["x!", () => push("!"), "op", "14px"],
    ["π", () => push("π"), "op", "15px"], ["e", () => push("E"), "op", "15px"],
    ["1/x", () => push("^-1"), "op", "13px"], ["x²", () => push("^2"), "op", "14px"],
    ["M+", () => memOp("+"), "util", "13px"], ["M−", () => memOp("-"), "util", "13px"],
    ["MR", () => memOp("r"), "util", "13px"], ["MC", () => memOp("c"), "util", "13px"],
  ];
  const keyStyle = (kind) => ({
    borderColor: kind === "op" ? "rgba(132,217,211,.45)" : kind === "util" ? "rgba(233,233,237,.16)" : "transparent",
    color: kind === "op" ? "#abfcf7" : kind === "util" ? "rgba(233,233,237,.7)" : "#e9e9ed",
    background: kind === "num" ? "rgba(233,233,237,.06)" : "transparent",
  });

  return (
    <div style={{ display: "flex", flexWrap: "wrap", gap: 14, alignItems: "flex-start" }}>
      <div style={{ flex: "1 1 300px", minWidth: 280, background: "#17233e", borderRadius: 14, padding: 14, boxShadow: "0 0 0 1px #3f424d" }}>
        <div style={{ display: "flex", alignItems: "center", gap: 8, marginBottom: 10 }}>
          <button className="btn" onClick={() => setDeg((d) => !d)} style={{ fontSize: 11, padding: "3px 9px", borderColor: "#84d9d3", color: "#84d9d3" }}>{deg ? "DEG" : "RAD"}</button>
          {mem !== 0 && <span className="tag tag-accent" style={{ fontSize: 10 }}>M {trimNum(mem)}</span>}
          <span style={{ marginLeft: "auto", fontSize: 11, color: "rgba(233,233,237,.4)" }}>키보드 입력 가능</span>
        </div>
        <div style={{ minHeight: 86, padding: "12px 14px", borderRadius: 8, background: "#11192c", display: "flex", flexDirection: "column", justifyContent: "flex-end", gap: 4, overflow: "hidden" }}>
          <div style={{ fontSize: 13, color: "rgba(233,233,237,.5)", wordBreak: "break-all", textAlign: "right", minHeight: 18, fontVariantNumeric: "tabular-nums" }}>{expr || " "}</div>
          <div style={{ fontSize: "clamp(26px,4vw,34px)", fontWeight: 500, textAlign: "right", wordBreak: "break-all", fontVariantNumeric: "tabular-nums", color: err ? "#abfcf7" : "#e9e9ed" }}>{out}</div>
        </div>
        <div style={{ display: "grid", gridTemplateColumns: "repeat(4,minmax(0,1fr))", gap: 7, marginTop: 12 }}>
          {numDefs.map((d, i) => <button key={i} className="btn" onClick={d[1]} style={{ minHeight: 46, fontSize: d[3] || "15px", ...keyStyle(d[2]) }}>{d[0]}</button>)}
        </div>
        <button className="btn btn-primary btn-block" onClick={evaluate} style={{ minHeight: 46, fontSize: 17, marginTop: 7 }}>=</button>
      </div>

      <div style={{ flex: "1 1 260px", minWidth: 250, background: "#17233e", borderRadius: 14, padding: 14, boxShadow: "0 0 0 1px #3f424d" }}>
        <div style={{ fontSize: 10, letterSpacing: ".1em", textTransform: "uppercase", color: "rgba(233,233,237,.45)", marginBottom: 10 }}>함수 · 상수 · 메모리</div>
        <div style={{ display: "grid", gridTemplateColumns: "repeat(4,minmax(0,1fr))", gap: 7 }}>
          {funcDefs.map((d, i) => <button key={i} className="btn" onClick={d[1]} style={{ minHeight: 44, fontSize: d[3] || "15px", ...keyStyle(d[2]) }}>{d[0]}</button>)}
        </div>
        <div style={{ marginTop: 12, fontSize: 11.5, lineHeight: 1.7, color: "rgba(233,233,237,.45)" }}>
          키보드 &nbsp;0-9 . + - * / ^ ( ) &nbsp;· Enter 계산 · Backspace 지우기 · Esc 초기화
        </div>
      </div>
    </div>
  );
}

/* ============================================================
   13. 데이터 입력 테이블
   ============================================================ */
function DataTable({ rows, setRows, tableWarn, onCompute }) {
  const inputRefs = useRef(new Map());

  function setCell(i, key, v) { setRows((rs) => rs.map((r, idx) => (idx === i ? { ...r, [key]: v } : r))); }
  function addRow() { setRows((rs) => rs.concat([{ x: "", y: "" }])); }
  function delRow(i) { setRows((rs) => { const n = rs.slice(); n.splice(i, 1); return n.length ? n : [{ x: "", y: "" }]; }); }
  function clearRows() { setRows(Array.from({ length: 5 }, () => ({ x: "", y: "" }))); }
  function loadSample() { setRows(sampleRows()); }

  function handlePaste(e, i, key) {
    const txt = (e.clipboardData || window.clipboardData).getData("text");
    if (!txt) return;
    const cells = parsePasteBlock(txt);
    if (!cells.length) return;
    e.preventDefault();
    setRows((rs) => {
      const rows2 = rs.map((r) => ({ ...r }));
      cells.forEach((c, k) => {
        const idx = i + k;
        while (rows2.length <= idx) rows2.push({ x: "", y: "" });
        if (key === "x") { if (c[0] !== undefined) rows2[idx].x = c[0].trim(); if (c[1] !== undefined) rows2[idx].y = c[1].trim(); }
        else { if (c[0] !== undefined) rows2[idx].y = c[0].trim(); }
      });
      return rows2;
    });
  }

  function cellKey(e, i, key) {
    if (e.key !== "Enter") return;
    e.preventDefault();
    const isLast = i === rows.length - 1;
    if (isLast) addRow();
    const flatIdx = i * 2 + (key === "y" ? 1 : 0);
    setTimeout(() => {
      const next = inputRefs.current.get(flatIdx + 2);
      if (next) next.focus();
    }, 20);
  }

  return (
    <div style={{ background: "#17233e", borderRadius: 14, boxShadow: "0 0 0 1px #3f424d", overflow: "hidden" }}>
      <div style={{ display: "flex", alignItems: "center", gap: 8, flexWrap: "wrap", padding: "11px 14px" }}>
        <span style={{ fontSize: 12, color: "rgba(233,233,237,.6)" }}>{rows.length}행 · X, Y 2열</span>
        {tableWarn && <span className="tag tag-accent" style={{ fontSize: 10.5 }}>{tableWarn}</span>}
        <div style={{ marginLeft: "auto", display: "flex", gap: 7, flexWrap: "wrap" }}>
          <button className="btn btn-secondary" onClick={addRow} style={{ fontSize: 12.5, padding: "5px 11px" }}>+ 행 추가</button>
          <button className="btn btn-secondary" onClick={loadSample} style={{ fontSize: 12.5, padding: "5px 11px" }}>예제 데이터</button>
          <button className="btn btn-secondary" onClick={clearRows} style={{ fontSize: 12.5, padding: "5px 11px" }}>전체 지우기</button>
        </div>
      </div>
      <div style={{ maxHeight: 340, overflow: "auto", padding: "0 6px" }}>
        <table className="table" style={{ minWidth: "100%" }}>
          <thead><tr><th style={{ width: 46 }}>#</th><th>X</th><th>Y</th><th style={{ width: 44 }}></th></tr></thead>
          <tbody>
            {rows.map((r, i) => {
              const badX = r.x.trim() !== "" && !isFinite(parseFloat(r.x));
              const badY = r.y.trim() !== "" && !isFinite(parseFloat(r.y));
              const half = (r.x.trim() === "") !== (r.y.trim() === "");
              const xb = badX ? "#abfcf7" : half && r.x.trim() === "" ? "rgba(171,252,247,.4)" : "rgba(233,233,237,.16)";
              const yb = badY ? "#abfcf7" : half && r.y.trim() === "" ? "rgba(171,252,247,.4)" : "rgba(233,233,237,.16)";
              return (
                <tr key={i}>
                  <td style={{ color: "rgba(233,233,237,.4)", fontSize: 12, fontVariantNumeric: "tabular-nums" }}>{i + 1}</td>
                  <td style={{ padding: "4px 6px" }}>
                    <input className="input" value={r.x} inputMode="decimal" style={{ minHeight: 34, fontVariantNumeric: "tabular-nums", borderColor: xb }}
                      ref={(el) => inputRefs.current.set(i * 2, el)}
                      onChange={(e) => setCell(i, "x", e.target.value)} onPaste={(e) => handlePaste(e, i, "x")} onKeyDown={(e) => cellKey(e, i, "x")} />
                  </td>
                  <td style={{ padding: "4px 6px" }}>
                    <input className="input" value={r.y} inputMode="decimal" style={{ minHeight: 34, fontVariantNumeric: "tabular-nums", borderColor: yb }}
                      ref={(el) => inputRefs.current.set(i * 2 + 1, el)}
                      onChange={(e) => setCell(i, "y", e.target.value)} onPaste={(e) => handlePaste(e, i, "y")} onKeyDown={(e) => cellKey(e, i, "y")} />
                  </td>
                  <td style={{ padding: "4px 6px" }}><button className="btn btn-icon" onClick={() => delRow(i)} title="행 삭제" style={{ width: 30, height: 30, color: "rgba(233,233,237,.45)" }}>×</button></td>
                </tr>
              );
            })}
          </tbody>
        </table>
      </div>
      <div style={{ display: "flex", alignItems: "center", gap: 10, flexWrap: "wrap", padding: "12px 14px", background: "rgba(233,233,237,.03)" }}>
        <span style={{ fontSize: 11.5, color: "rgba(233,233,237,.45)" }}>계산은 자동이 아닙니다 — 확인을 눌러 결과를 산출하세요.</span>
        <button className="btn btn-primary" onClick={onCompute} style={{ marginLeft: "auto", minHeight: 38, padding: "0 22px", fontSize: 14 }}>확인</button>
      </div>
    </div>
  );
}

/* ============================================================
   14. 결과 패널 (수치 · 표 · 차트 · 복사)
   ============================================================ */
function CopyButton({ label, onClick }) {
  const [copied, setCopied] = useState(false);
  return <button className="btn btn-secondary" onClick={() => onClick(() => { setCopied(true); setTimeout(() => setCopied(false), 1600); })} style={{ fontSize: 12, padding: "4px 10px" }}>
    {copied ? "복사됨" : label}
  </button>;
}
function SaveButton({ onSave }) {
  const [state, setState] = useState("idle"); // idle | saving | saved | error
  return <button className="btn btn-secondary" disabled={state === "saving"} onClick={async () => {
    setState("saving");
    try { await onSave(); setState("saved"); } catch (e) { setState("error"); }
    setTimeout(() => setState("idle"), 1600);
  }} style={{ fontSize: 12, padding: "4px 10px" }}>
    {state === "saving" ? "저장 중…" : state === "saved" ? "저장됨" : state === "error" ? "저장 실패" : "저장"}
  </button>;
}
function ChartCard({ title, subtitle, id, onDownload, children, extra, caption }) {
  return (
    <div style={{ flex: "1 1 380px", minWidth: 300, background: "#17233e", borderRadius: 14, padding: "clamp(13px,2vw,18px)", boxShadow: "0 0 0 1px #3f424d" }}>
      <div style={{ display: "flex", alignItems: "baseline", gap: 8, flexWrap: "wrap", marginBottom: 6 }}>
        <h5 style={{ margin: 0, fontSize: 15 }}>{title} <span style={{ fontSize: 11, color: "rgba(233,233,237,.4)", fontWeight: 400 }}>{subtitle}</span></h5>
        <div style={{ display: "flex", gap: 6, marginLeft: "auto", flexWrap: "wrap" }}>
          {extra}
          <button className="btn btn-secondary" onClick={() => onDownload(id)} style={{ fontSize: 11.5, padding: "3px 9px" }}>PNG 저장</button>
        </div>
      </div>
      <svg id={id} viewBox="0 0 560 320" style={{ width: "100%", height: "auto", display: "block" }}>
        <rect x="0" y="0" width="560" height="320" fill="#17233e" />
        {children}
      </svg>
      {caption && <p style={{ margin: "10px 0 0", fontSize: 12, lineHeight: 1.55, color: "rgba(233,233,237,.6)" }}>{caption}</p>}
    </div>
  );
}
function ScaleToggle({ on, setOn, disabledHint }) {
  if (disabledHint) return <span style={{ fontSize: 10.5, color: "rgba(233,233,237,.32)", alignSelf: "center" }}>{disabledHint}</span>;
  return (
    <>
      <button className="btn" onClick={() => setOn(false)} style={{ fontSize: 11.5, padding: "3px 9px", borderColor: !on ? "#84d9d3" : "rgba(233,233,237,.16)", color: !on ? "#84d9d3" : "rgba(233,233,237,.55)", background: !on ? "rgba(132,217,211,.12)" : "transparent" }}>선형</button>
      <button className="btn" onClick={() => setOn(true)} style={{ fontSize: 11.5, padding: "3px 9px", borderColor: on ? "#84d9d3" : "rgba(233,233,237,.16)", color: on ? "#84d9d3" : "rgba(233,233,237,.55)", background: on ? "rgba(132,217,211,.12)" : "transparent" }}>log</button>
    </>
  );
}
function ResultsPanel({ result, tableWarn, emptyMsg, logX, setLogX, logY, setLogY, onSave }) {
  const R = result;
  const charts = useMemo(() => (R ? buildCharts(R, logX && R.logOk, logY) : null), [R, logX, logY]);

  if (!R) {
    return <div style={{ marginTop: 14, padding: "34px 20px", borderRadius: 14, background: "#17233e", boxShadow: "0 0 0 1px #3f424d", textAlign: "center" }}>
      <div style={{ fontSize: 14, color: "rgba(233,233,237,.6)" }}>{emptyMsg}</div>
    </div>;
  }

  const sign = R.a >= 0 ? "+" : "−";
  const eq = "y = " + fmt(R.b, 4) + " x " + sign + " " + fmt(Math.abs(R.a), 4);
  const metrics = [
    { k: "결정계수 R²", v: fmt(R.R2, 5), en: "R-squared" },
    { k: "수정 R²", v: fmt(R.adjR2, 5), en: "adjusted R²" },
    { k: "상관계수 r", v: fmt(R.r, 5), en: "Pearson r" },
    { k: "잔차표준편차 Syx", v: fmt(R.Syx, 4), en: "residual SD" },
    { k: "LOD", v: fmt(R.LOD, 4), en: "limit of detection" },
    { k: "LOQ", v: fmt(R.LOQ, 4), en: "limit of quantitation" },
    { k: "회수율", v: fmt(R.recovery, 2) + " %", en: "recovery" },
    { k: "%RSD", v: fmt(R.rsd, 2) + " %", en: "relative SD" },
    { k: "t 통계량", v: fmt(R.tB, 3), en: "t-statistic (slope)" },
    { k: "p 값", v: fmtP(R.pB), en: "p-value (slope)" },
  ];
  const ciRows = [
    { name: "기울기 (slope)", est: fmt(R.b, 5), se: fmt(R.seB, 5), lo: fmt(R.b - R.tc * R.seB, 5), hi: fmt(R.b + R.tc * R.seB, 5) },
    { name: "절편 (intercept)", est: fmt(R.a, 5), se: fmt(R.seA, 5), lo: fmt(R.a - R.tc * R.seA, 5), hi: fmt(R.a + R.tc * R.seA, 5) },
  ];
  const anovaRows = [
    { src: "회귀 (regression)", df: 1, ss: fmt(R.SSR, 4), ms: fmt(R.SSR, 4), f: fmt(R.F, 3), p: fmtP(R.pF) },
    { src: "잔차 (residual)", df: R.dfRes, ss: fmt(R.SSE, 4), ms: fmt(R.MSE, 5), f: "—", p: "—" },
    { src: "전체 (total)", df: R.n - 1, ss: fmt(R.SST, 4), ms: "—", f: "—", p: "—" },
  ];
  const verdict = (p, okText, badText) => !isFinite(p) ? { verdict: "산출 불가", vbg: "#3f424d", vfg: "#e4e7f5" }
    : (p >= 0.05 ? { verdict: okText, vbg: "#3a6a67", vfg: "#e5fefc" } : { verdict: badText, vbg: "#529490", vfg: "#f4fffe" });
  const testRows = [
    { name: "회귀 유의성 검정", en: "F-test of regression", stat: "F = " + fmt(R.F, 3) + " (df 1, " + R.dfRes + ")", p: fmtP(R.pF),
      vbg: R.pF < 0.05 ? "#3a6a67" : "#3f424d", vfg: "#e5fefc", verdict: R.pF < 0.05 ? "회귀 유의" : "유의하지 않음" },
    { name: "기울기 검정 (H₀: b = 0)", en: "t-test, slope", stat: "t = " + fmt(R.tB, 3) + " (df " + R.dfRes + ")", p: fmtP(R.pB),
      vbg: R.pB < 0.05 ? "#3a6a67" : "#3f424d", vfg: "#e5fefc", verdict: R.pB < 0.05 ? "기울기 유의" : "유의하지 않음" },
    { name: "절편 검정 (H₀: a = 0)", en: "t-test, intercept", stat: "t = " + fmt(R.tA, 3) + " (df " + R.dfRes + ")", p: fmtP(R.pA),
      vbg: R.pA < 0.05 ? "#529490" : "#3a6a67", vfg: "#f4fffe", verdict: R.pA < 0.05 ? "절편 0과 유의하게 다름" : "절편 0과 차이 없음" },
    { name: "상관계수 검정 (H₀: ρ = 0)", en: "t-test, Pearson r", stat: "t = " + fmt(R.tR, 3) + " (df " + R.dfRes + ")", p: fmtP(R.pR),
      vbg: R.pR < 0.05 ? "#3a6a67" : "#3f424d", vfg: "#e5fefc", verdict: R.pR < 0.05 ? "상관 유의" : "유의하지 않음" },
    Object.assign({ name: "적합결여 검정", en: "Lack-of-fit test", stat: R.lof ? "F = " + fmt(R.lof.F, 3) + " (df " + R.lof.df + ")" : "반복 측정 필요", p: R.lof ? fmtP(R.lof.p) : "—" }, verdict(R.lof ? R.lof.p : NaN, "선형 모형 적합", "적합결여 의심")),
    Object.assign({ name: "등분산성 검정", en: "Levene's test", stat: R.lev ? "W = " + fmt(R.lev.W, 3) + " (df " + R.lev.df + ")" : "산출 불가 — 수준별 3회 이상 반복 필요", p: R.lev ? fmtP(R.lev.p) : "—" }, verdict(R.lev ? R.lev.p : NaN, "등분산 가정 유지", "등분산 위반 의심")),
    Object.assign({ name: "정규성 검정 (잔차)", en: "Shapiro-Francia W′", stat: "W′ = " + fmt(R.Wsf, 4), p: fmtP(R.pSF) }, verdict(R.pSF, "정규성 유지", "정규성 위반 의심")),
    Object.assign({ name: "이상치 검정", en: "Grubbs' test", stat: "G = " + fmt(R.G, 3), p: fmtP(R.pG) }, verdict(R.pG, "이상치 없음", "이상치 의심")),
    { name: "영향점 진단", en: "Cook's distance (max)", stat: "D = " + fmt(R.cookMax, 4), p: "—",
      vbg: R.cookMax > 1 ? "#529490" : "#3a6a67", vfg: "#f4fffe", verdict: R.cookMax > 1 ? "영향점 검토 필요" : "기준(1) 이내" },
    { name: "잔차 자기상관 검정", en: "Durbin-Watson", stat: "d = " + fmt(R.DW, 3), p: "—",
      vbg: (R.DW > 1.5 && R.DW < 2.5) ? "#3a6a67" : "#529490", vfg: "#f4fffe",
      verdict: !isFinite(R.DW) ? "산출 불가" : (R.DW > 1.5 && R.DW < 2.5) ? "자기상관 없음" : (R.DW <= 1.5 ? "양의 자기상관 의심" : "음의 자기상관 의심") },
  ];

  const ciT = [["항목", "추정값", "표준오차", "95% 하한", "95% 상한"]].concat(ciRows.map((r) => [r.name, r.est, r.se, r.lo, r.hi]));
  const anT = [["요인", "df", "SS", "MS", "F", "p"]].concat(anovaRows.map((r) => [r.src, r.df, r.ss, r.ms, r.f, r.p]));
  const tsT = [["검정", "통계량", "p", "판정"]].concat(testRows.map((r) => [r.name + " / " + r.en, r.stat, r.p, r.verdict]));
  const mT = [["항목", "값"]].concat(metrics.map((m) => [m.k + " (" + m.en + ")", m.v]));

  const copy = (text, html, done) => copyToClipboard(text, html, done);
  const lgOn = logX && R.logOk;
  const lgYOn = logY && charts.catLogOk;

  return (
    <div style={{ display: "flex", flexDirection: "column", gap: 16, marginTop: 14 }}>
      <div style={{ background: "#17233e", borderRadius: 14, padding: "clamp(14px,2vw,20px)", boxShadow: "0 0 0 1px #595d6c" }}>
        <div style={{ display: "flex", alignItems: "baseline", gap: 10, flexWrap: "wrap", marginBottom: 10 }}>
          <span style={{ fontSize: 10, letterSpacing: ".1em", textTransform: "uppercase", color: "#84d9d3" }}>회귀식 · Regression equation</span>
          <div style={{ marginLeft: "auto" }}><CopyButton label="수식 복사" onClick={(done) => copy(eq, null, done)} /></div>
        </div>
        <div style={{ fontSize: "clamp(20px,3vw,30px)", fontWeight: 500, fontVariantNumeric: "tabular-nums", letterSpacing: "-.01em", wordBreak: "break-word" }}>{eq}</div>
        <div style={{ marginTop: 8, fontSize: 12.5, color: "rgba(233,233,237,.5)", fontVariantNumeric: "tabular-nums" }}>n = {R.n} · 자유도(df) = {R.dfRes} · 신뢰수준 95%</div>
      </div>

      <div style={{ display: "grid", gridTemplateColumns: "repeat(auto-fit,minmax(148px,1fr))", gap: 10 }}>
        {metrics.map((m, i) => (
          <div key={i} style={{ background: "#17233e", borderRadius: 8, padding: "12px 13px", boxShadow: "0 0 0 1px #3f424d", display: "flex", flexDirection: "column", gap: 3 }}>
            <span style={{ fontSize: 11, color: "rgba(233,233,237,.55)" }}>{m.k}</span>
            <span style={{ fontSize: 20, fontWeight: 500, fontVariantNumeric: "tabular-nums" }}>{m.v}</span>
            <span style={{ fontSize: 10, letterSpacing: ".03em", color: "rgba(233,233,237,.35)" }}>{m.en}</span>
          </div>
        ))}
      </div>

      <div style={{ display: "flex", flexWrap: "wrap", gap: 16 }}>
        <div style={{ flex: "1 1 340px", minWidth: 300, background: "#17233e", borderRadius: 14, padding: "clamp(13px,2vw,18px)", boxShadow: "0 0 0 1px #3f424d" }}>
          <div style={{ display: "flex", alignItems: "baseline", gap: 8, marginBottom: 8 }}>
            <h5 style={{ margin: 0, fontSize: 15 }}>신뢰구간 <span style={{ fontSize: 11, color: "rgba(233,233,237,.4)", fontWeight: 400 }}>Confidence interval (95%)</span></h5>
            <div style={{ marginLeft: "auto" }}><CopyButton label="표 복사" onClick={(done) => copy(tsv(ciT), htmlTable(ciT), done)} /></div>
          </div>
          <div style={{ overflowX: "auto" }}>
            <table className="table" style={{ fontSize: 13, minWidth: 420 }}>
              <thead><tr><th>항목</th><th>추정값</th><th>표준오차</th><th>95% 하한</th><th>95% 상한</th></tr></thead>
              <tbody>{ciRows.map((c, i) => <tr key={i}><td>{c.name}</td><td style={{ fontVariantNumeric: "tabular-nums" }}>{c.est}</td><td style={{ fontVariantNumeric: "tabular-nums" }}>{c.se}</td><td style={{ fontVariantNumeric: "tabular-nums" }}>{c.lo}</td><td style={{ fontVariantNumeric: "tabular-nums" }}>{c.hi}</td></tr>)}</tbody>
            </table>
          </div>
        </div>

        <div style={{ flex: "1 1 340px", minWidth: 300, background: "#17233e", borderRadius: 14, padding: "clamp(13px,2vw,18px)", boxShadow: "0 0 0 1px #3f424d" }}>
          <div style={{ display: "flex", alignItems: "baseline", gap: 8, marginBottom: 8 }}>
            <h5 style={{ margin: 0, fontSize: 15 }}>회귀 분산분석표 <span style={{ fontSize: 11, color: "rgba(233,233,237,.4)", fontWeight: 400 }}>ANOVA</span></h5>
            <div style={{ marginLeft: "auto" }}><CopyButton label="표 복사" onClick={(done) => copy(tsv(anT), htmlTable(anT), done)} /></div>
          </div>
          <div style={{ overflowX: "auto" }}>
            <table className="table" style={{ fontSize: 13, minWidth: 420 }}>
              <thead><tr><th>요인</th><th>df</th><th>SS</th><th>MS</th><th>F</th><th>p</th></tr></thead>
              <tbody>{anovaRows.map((a, i) => <tr key={i}><td>{a.src}</td><td style={{ fontVariantNumeric: "tabular-nums" }}>{a.df}</td><td style={{ fontVariantNumeric: "tabular-nums" }}>{a.ss}</td><td style={{ fontVariantNumeric: "tabular-nums" }}>{a.ms}</td><td style={{ fontVariantNumeric: "tabular-nums" }}>{a.f}</td><td style={{ fontVariantNumeric: "tabular-nums" }}>{a.p}</td></tr>)}</tbody>
            </table>
          </div>
        </div>
      </div>

      <div style={{ background: "#17233e", borderRadius: 14, padding: "clamp(13px,2vw,18px)", boxShadow: "0 0 0 1px #3f424d" }}>
        <div style={{ display: "flex", alignItems: "baseline", gap: 8, marginBottom: 8, flexWrap: "wrap" }}>
          <h5 style={{ margin: 0, fontSize: 15 }}>진단 · 검정 <span style={{ fontSize: 11, color: "rgba(233,233,237,.4)", fontWeight: 400 }}>Diagnostics &amp; tests</span></h5>
          <div style={{ marginLeft: "auto" }}><CopyButton label="표 복사" onClick={(done) => copy(tsv(tsT), htmlTable(tsT), done)} /></div>
        </div>
        <div style={{ overflowX: "auto" }}>
          <table className="table" style={{ fontSize: 13, minWidth: 520 }}>
            <thead><tr><th>검정</th><th>통계량</th><th>p</th><th>판정</th></tr></thead>
            <tbody>
              {testRows.map((t, i) => (
                <tr key={i}>
                  <td><span style={{ display: "block" }}>{t.name}</span><span style={{ fontSize: 10.5, color: "rgba(233,233,237,.35)" }}>{t.en}</span></td>
                  <td style={{ fontVariantNumeric: "tabular-nums" }}>{t.stat}</td>
                  <td style={{ fontVariantNumeric: "tabular-nums" }}>{t.p}</td>
                  <td><span className="tag" style={{ fontSize: 10.5, background: t.vbg, color: t.vfg }}>{t.verdict}</span></td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </div>

      <div style={{ display: "flex", flexWrap: "wrap", gap: 16 }}>
        <ChartCard title="검량선 · 신뢰대역" subtitle="Fit with confidence & prediction bands" id="ch-fit" onDownload={(id) => exportSvgAsPng(id, "regression-fit")}
          extra={<ScaleToggle on={lgOn} setOn={setLogX} disabledHint={!R.logOk ? "X ≤ 0 포함 — log 불가" : null} />}
          caption={captionFit(R, lgOn)}>
          {charts.fit.yt.map((t, i) => <line key={i} x1="52" x2="544" y1={t.y} y2={t.y} stroke="rgba(233,233,237,.07)" strokeWidth="1" />)}
          <path d={charts.fit.pi} fill="rgba(132,217,211,.10)" />
          <path d={charts.fit.ci} fill="rgba(132,217,211,.22)" />
          <path d={charts.fit.line} stroke="#abfcf7" strokeWidth="1.8" fill="none" />
          {charts.fit.pts.map((p, i) => <circle key={i} cx={p.cx} cy={p.cy} r="3.6" fill="#e9e9ed" />)}
          <line x1="52" x2="544" y1="280" y2="280" stroke="rgba(233,233,237,.25)" />
          <line x1="52" x2="52" y1="14" y2="280" stroke="rgba(233,233,237,.25)" />
          {charts.fit.xt.map((t, i) => <text key={i} x={t.x} y="298" fill="rgba(233,233,237,.45)" fontSize="10.5" textAnchor="middle">{t.label}</text>)}
          {charts.fit.yt.map((t, i) => <text key={i} x="46" y={t.ty} fill="rgba(233,233,237,.45)" fontSize="10.5" textAnchor="end">{t.label}</text>)}
          <text x="544" y="314" fill="rgba(233,233,237,.35)" fontSize="10" textAnchor="end">X</text>
          <text x="10" y="20" fill="rgba(233,233,237,.35)" fontSize="10">Y</text>
        </ChartCard>

        <ChartCard title="잔차 그림" subtitle="Residual plot" id="ch-resid" onDownload={(id) => exportSvgAsPng(id, "residual-plot")}
          extra={<ScaleToggle on={lgOn} setOn={setLogX} disabledHint={!R.logOk ? "X ≤ 0 포함 — log 불가" : null} />}
          caption={captionResid(R)}>
          {charts.resid.yt.map((t, i) => <line key={i} x1="52" x2="544" y1={t.y} y2={t.y} stroke="rgba(233,233,237,.07)" />)}
          <line x1="52" x2="544" y1={charts.resid.zero} y2={charts.resid.zero} stroke="#84d9d3" strokeWidth="1.4" strokeDasharray="5 4" />
          {charts.resid.pts.map((p, i) => <circle key={i} cx={p.cx} cy={p.cy} r="3.6" fill="#e9e9ed" />)}
          <line x1="52" x2="544" y1="280" y2="280" stroke="rgba(233,233,237,.25)" />
          <line x1="52" x2="52" y1="14" y2="280" stroke="rgba(233,233,237,.25)" />
          {charts.resid.xt.map((t, i) => <text key={i} x={t.x} y="298" fill="rgba(233,233,237,.45)" fontSize="10.5" textAnchor="middle">{t.label}</text>)}
          {charts.resid.yt.map((t, i) => <text key={i} x="46" y={t.ty} fill="rgba(233,233,237,.45)" fontSize="10.5" textAnchor="end">{t.label}</text>)}
          <text x="544" y="314" fill="rgba(233,233,237,.35)" fontSize="10" textAnchor="end">적합값 X</text>
          <text x="10" y="20" fill="rgba(233,233,237,.35)" fontSize="10">e</text>
        </ChartCard>

        <ChartCard title="상자 그림" subtitle="Box plot by X" id="ch-box" onDownload={(id) => exportSvgAsPng(id, "box-plot")}
          extra={<ScaleToggle on={lgYOn} setOn={setLogY} disabledHint={!charts.catLogOk ? "Y ≤ 0 포함 — log 불가" : null} />}
          caption={captionBox(R)}>
          {charts.box.yt.map((t, i) => <line key={i} x1="52" x2="544" y1={t.y} y2={t.y} stroke="rgba(233,233,237,.07)" />)}
          {charts.box.groups.map((g, i) => (
            <g key={i}>
              <line x1={g.cx} x2={g.cx} y1={g.hi} y2={g.lo} stroke="rgba(233,233,237,.45)" />
              <line x1={g.wl} x2={g.wr} y1={g.hi} y2={g.hi} stroke="rgba(233,233,237,.45)" />
              <line x1={g.wl} x2={g.wr} y1={g.lo} y2={g.lo} stroke="rgba(233,233,237,.45)" />
              <rect x={g.bx} y={g.q3} width={g.bw} height={g.bh} fill="rgba(132,217,211,.20)" stroke="#84d9d3" />
              <line x1={g.bx} x2={g.br} y1={g.med} y2={g.med} stroke="#cefdfa" strokeWidth="2" />
              <text x={g.cx} y="298" fill="rgba(233,233,237,.45)" fontSize="10.5" textAnchor="middle">{g.label}</text>
            </g>
          ))}
          <line x1="52" x2="544" y1="280" y2="280" stroke="rgba(233,233,237,.25)" />
          <line x1="52" x2="52" y1="14" y2="280" stroke="rgba(233,233,237,.25)" />
          {charts.box.yt.map((t, i) => <text key={i} x="46" y={t.ty} fill="rgba(233,233,237,.45)" fontSize="10.5" textAnchor="end">{t.label}</text>)}
          <text x="10" y="20" fill="rgba(233,233,237,.35)" fontSize="10">Y</text>
        </ChartCard>

        <ChartCard title="개별값 그림" subtitle="Individual value plot" id="ch-ind" onDownload={(id) => exportSvgAsPng(id, "individual-value-plot")}
          extra={<ScaleToggle on={lgYOn} setOn={setLogY} disabledHint={!charts.catLogOk ? "Y ≤ 0 포함 — log 불가" : null} />}
          caption={captionInd(R)}>
          {charts.ind.yt.map((t, i) => <line key={i} x1="52" x2="544" y1={t.y} y2={t.y} stroke="rgba(233,233,237,.07)" />)}
          {charts.ind.dots.map((p, i) => <circle key={i} cx={p.cx} cy={p.cy} r="3.4" fill="#e9e9ed" opacity="0.85" />)}
          {charts.ind.groups.map((g, i) => (
            <g key={i}>
              <line x1={g.wl} x2={g.wr} y1={g.mean} y2={g.mean} stroke="#84d9d3" strokeWidth="1.6" />
              <text x={g.cx} y="298" fill="rgba(233,233,237,.45)" fontSize="10.5" textAnchor="middle">{g.label}</text>
            </g>
          ))}
          <line x1="52" x2="544" y1="280" y2="280" stroke="rgba(233,233,237,.25)" />
          <line x1="52" x2="52" y1="14" y2="280" stroke="rgba(233,233,237,.25)" />
          {charts.ind.yt.map((t, i) => <text key={i} x="46" y={t.ty} fill="rgba(233,233,237,.45)" fontSize="10.5" textAnchor="end">{t.label}</text>)}
        </ChartCard>

        <ChartCard title="구간 그림" subtitle="Interval plot, mean ± 95% CI" id="ch-int" onDownload={(id) => exportSvgAsPng(id, "interval-plot")}
          extra={<ScaleToggle on={lgYOn} setOn={setLogY} disabledHint={!charts.catLogOk ? "Y ≤ 0 포함 — log 불가" : null} />}
          caption={captionInt(charts.intv.stats)}>
          {charts.intv.yt.map((t, i) => <line key={i} x1="52" x2="544" y1={t.y} y2={t.y} stroke="rgba(233,233,237,.07)" />)}
          {charts.intv.groups.map((g, i) => (
            <g key={i}>
              <line x1={g.cx} x2={g.cx} y1={g.hi} y2={g.lo} stroke="#84d9d3" strokeWidth="1.6" />
              <line x1={g.wl} x2={g.wr} y1={g.hi} y2={g.hi} stroke="#84d9d3" strokeWidth="1.6" />
              <line x1={g.wl} x2={g.wr} y1={g.lo} y2={g.lo} stroke="#84d9d3" strokeWidth="1.6" />
              <circle cx={g.cx} cy={g.mean} r="4.2" fill="#e9e9ed" />
              <text x={g.cx} y="298" fill="rgba(233,233,237,.45)" fontSize="10.5" textAnchor="middle">{g.label}</text>
            </g>
          ))}
          <line x1="52" x2="544" y1="280" y2="280" stroke="rgba(233,233,237,.25)" />
          <line x1="52" x2="52" y1="14" y2="280" stroke="rgba(233,233,237,.25)" />
          {charts.intv.yt.map((t, i) => <text key={i} x="46" y={t.ty} fill="rgba(233,233,237,.45)" fontSize="10.5" textAnchor="end">{t.label}</text>)}
        </ChartCard>
      </div>

      <div style={{ display: "flex", alignItems: "center", gap: 10, flexWrap: "wrap", padding: "14px 16px", borderRadius: 14, background: "#141d34", boxShadow: "0 0 0 1px #3f424d" }}>
        <span style={{ fontSize: 12, color: "rgba(233,233,237,.5)", maxWidth: "52ch" }}>수치·통계표는 서식 있는 표와 plain text 로, 수식은 텍스트로 복사됩니다. 가중회귀(1/x, 1/x²)와 전체 리포트 파일 내보내기는 v2 예정입니다.</span>
        <div style={{ marginLeft: "auto", display: "flex", gap: 8 }}>
          <CopyButton label="전체 결과 복사" onClick={(done) => copy(
            eq + "\n\n" + tsv(mT) + "\n\n" + tsv(ciT) + "\n\n" + tsv(anT) + "\n\n" + tsv(tsT),
            "<p>" + eq + "</p>" + htmlTable(mT) + htmlTable(ciT) + htmlTable(anT) + htmlTable(tsT),
            done
          )} />
          {onSave && <SaveButton onSave={onSave} />}
        </div>
      </div>
    </div>
  );
}

/* ============================================================
   15. 기록 열람 화면
   ============================================================ */
function formatHistoryLabel(createdAt) {
  let d;
  if (createdAt && typeof createdAt.toDate === "function") d = createdAt.toDate();
  else if (createdAt instanceof Date) d = createdAt;
  else if (createdAt) d = new Date(createdAt);
  else return "";
  if (!d || isNaN(d.getTime())) return "";
  const p = (n) => String(n).padStart(2, "0");
  return d.getFullYear() + "-" + p(d.getMonth() + 1) + "-" + p(d.getDate()) + " " + p(d.getHours()) + ":" + p(d.getMinutes());
}
function HistoryScreen({ history, onSelect }) {
  const slots = Array.from({ length: window.EgCalHistory ? window.EgCalHistory.HISTORY_LIMIT : 10 }, (_, i) => history[i] || null);
  return (
    <section>
      <span style={{ fontSize: 10, letterSpacing: ".1em", textTransform: "uppercase", color: "#84d9d3" }}>기록 · History</span>
      <h3 style={{ fontSize: "clamp(20px,2.4vw,25px)", margin: "0 0 6px" }}>저장된 결과 기록</h3>
      <p style={{ fontSize: 13, color: "rgba(233,233,237,.55)", margin: "0 0 18px", maxWidth: "60ch" }}>
        산출 결과 화면의 "저장" 버튼을 누르면 이 계정에 최신순으로 최대 {window.EgCalHistory ? window.EgCalHistory.HISTORY_LIMIT : 10}개까지 보관됩니다. 항목을 누르면 그 시점의 데이터와 결과를 다시 확인할 수 있습니다.
      </p>
      <div style={{ display: "flex", flexDirection: "column", gap: 10 }}>
        {slots.map((rec, i) => (
          <button key={i} className="btn" disabled={!rec} onClick={() => rec && onSelect(rec)}
            style={{
              minHeight: 52, width: "100%", justifyContent: "flex-start", padding: "0 18px", fontSize: 14,
              background: "#17233e", boxShadow: "0 0 0 1px #3f424d", borderColor: "transparent",
              color: rec ? "#e9e9ed" : "rgba(233,233,237,.4)", fontVariantNumeric: "tabular-nums",
            }}>
            {rec ? formatHistoryLabel(rec.createdAt) : "데이터 없음"}
          </button>
        ))}
      </div>
      {!window.EgCalHistory?.isConfigured && (
        <p style={{ marginTop: 18, fontSize: 11.5, color: "rgba(233,233,237,.4)" }}>
          ⚠ firebase-config.js 에 Firebase 프로젝트 설정을 입력하고 Firestore Database 를 생성해야 기록 저장이 동작합니다.
        </p>
      )}
    </section>
  );
}

/* ============================================================
   16. 메인 도구 페이지 (/app)
   ============================================================ */
function AppScreen({ userEmail, userId, onLogout }) {
  const [view, setView] = useState("main"); // main | history
  const [rows, setRows] = useState(sampleRows());
  const [result, setResult] = useState(null);
  const [tableWarn, setTableWarn] = useState("");
  const [emptyMsg, setEmptyMsg] = useState("데이터를 입력하고 확인을 누르면 결과가 산출됩니다.");
  const [logX, setLogX] = useState(false);
  const [logY, setLogY] = useState(false);
  const [history, setHistory] = useState([]);

  function compute(withRows) {
    const r = runRegression(withRows || rows);
    setResult(r.result); setTableWarn(r.tableWarn); setEmptyMsg(r.emptyMsg);
  }
  useEffect(() => { compute(); }, []); // eslint-disable-line

  const refreshHistory = useCallback(() => {
    if (!userId || !window.EgCalHistory) return;
    window.EgCalHistory.list(userId).then(setHistory).catch(() => {});
  }, [userId]);
  useEffect(() => { refreshHistory(); }, [refreshHistory]);

  async function saveCurrentResult() {
    if (!result || !userId || !window.EgCalHistory) throw new Error("cannot-save");
    const timeout = new Promise((_, reject) => setTimeout(() => reject(new Error("save-timeout")), 10000));
    await Promise.race([window.EgCalHistory.save(userId, { rows, logX, logY }), timeout]);
    refreshHistory();
  }

  function openHistoryRecord(rec) {
    setRows(rec.rows);
    setLogX(!!rec.logX);
    setLogY(!!rec.logY);
    compute(rec.rows);
    setView("main");
  }

  return (
    <div style={{ animation: "noct-in .28s ease" }}>
      <div style={{ position: "sticky", top: 0, zIndex: 20, background: "#11192c" }}>
        <div style={{ display: "flex", alignItems: "center", gap: 12, flexWrap: "wrap", padding: "12px clamp(14px,3vw,26px)" }}>
          <button className="btn" onClick={() => setView("main")} style={{ display: "flex", alignItems: "center", gap: 8, marginRight: "auto", padding: 0, color: "#e9e9ed" }}>
            <Logo /><span style={{ fontSize: 15, fontWeight: 500 }}>Eg-Cal : 공학용 연산 도우미</span>
          </button>
          <button className="btn btn-secondary" onClick={() => setView("history")} style={{ fontSize: 12.5, padding: "5px 11px" }}>기록</button>
          <span className="tag tag-neutral" style={{ fontSize: 10.5 }}>{userEmail}</span>
          <button className="btn btn-secondary" onClick={onLogout} style={{ fontSize: 12.5, padding: "5px 11px" }}>로그아웃</button>
        </div>
        <div style={{ height: 1, background: "linear-gradient(to right,transparent,rgba(233,233,237,.14) 48px,rgba(233,233,237,.14) calc(100% - 48px),transparent)" }} />
      </div>

      <div style={{ padding: "clamp(18px,3vw,34px) clamp(14px,3vw,26px) 80px", display: "flex", flexDirection: "column", gap: "clamp(28px,4vw,46px)" }}>
        {view === "history" ? (
          <HistoryScreen history={history} onSelect={openHistoryRecord} />
        ) : (
          <>
            <section>
              <span style={{ fontSize: 10, letterSpacing: ".1em", textTransform: "uppercase", color: "#84d9d3" }}>01 · Calculator</span>
              <h3 style={{ fontSize: "clamp(20px,2.4vw,25px)", margin: "0 0 6px" }}>공학용 계산기</h3>
              <p style={{ fontSize: 13, color: "rgba(233,233,237,.55)", margin: "0 0 18px", maxWidth: "56ch" }}>마우스 클릭과 키보드 입력을 함께 지원합니다. 계산 결과는 아래 표에 직접 입력하세요.</p>
              <Calculator />
            </section>

            <section>
              <span style={{ fontSize: 10, letterSpacing: ".1em", textTransform: "uppercase", color: "#84d9d3" }}>02 · Data input</span>
              <h3 style={{ fontSize: "clamp(20px,2.4vw,25px)", margin: "2px 0 6px" }}>데이터 입력</h3>
              <p style={{ fontSize: 13, color: "rgba(233,233,237,.55)", margin: "0 0 16px", maxWidth: "60ch" }}>X(인자) · Y(반응) 2열 구조입니다. 엑셀에서 복사한 여러 행을 셀에 바로 붙여넣을 수 있고, 행이 부족하면 자동으로 추가됩니다. Tab · Enter 로 셀 사이를 이동합니다.</p>
              <DataTable rows={rows} setRows={setRows} tableWarn={tableWarn} onCompute={() => compute()} />
            </section>

            <section>
              <span style={{ fontSize: 10, letterSpacing: ".1em", textTransform: "uppercase", color: "#84d9d3" }}>03 · Results</span>
              <h3 style={{ fontSize: "clamp(20px,2.4vw,25px)", margin: "2px 0 6px" }}>산출 결과</h3>
              <ResultsPanel result={result} tableWarn={tableWarn} emptyMsg={emptyMsg} logX={logX} setLogX={setLogX} logY={logY} setLogY={setLogY} onSave={saveCurrentResult} />
            </section>
          </>
        )}
      </div>
    </div>
  );
}

/* ============================================================
   17. 404
   ============================================================ */
function NotFoundScreen({ loggedIn, navigate }) {
  return (
    <div style={{ minHeight: "100vh", display: "flex", flexDirection: "column", justifyContent: "center", padding: "48px 28px", animation: "noct-in .28s ease" }}>
      <div style={{ width: "100%", maxWidth: 420, margin: "0 auto" }}>
        <div style={{ fontSize: "clamp(56px,12vw,88px)", fontWeight: 500, lineHeight: 1, letterSpacing: "-.03em", color: "#529490" }}>404</div>
        <h2 style={{ fontSize: "clamp(22px,3vw,29px)", margin: "14px 0 8px" }}>페이지를 찾을 수 없습니다</h2>
        <p style={{ fontSize: 13.5, color: "rgba(233,233,237,.55)", margin: "0 0 24px", maxWidth: "36ch" }}>주소가 변경되었거나 삭제된 경로입니다. 아래 버튼으로 이동하세요.</p>
        <div style={{ height: 1, margin: "0 0 22px", background: "linear-gradient(to right,transparent,rgba(233,233,237,.14) 40px,rgba(233,233,237,.14) calc(100% - 40px),transparent)" }} />
        <button className="btn btn-primary" onClick={() => navigate(loggedIn ? "/app" : "/login")} style={{ minHeight: 40, padding: "0 20px", fontSize: 14 }}>
          {loggedIn ? "메인 도구로 이동" : "로그인 페이지로 이동"}
        </button>
      </div>
    </div>
  );
}

/* ============================================================
   18. 앱 루트 — 라우팅 + 인증 가드 (Sitemap.md 라우팅 표 참고)
   ============================================================ */
function App() {
  const { path, navigate } = useRouter();
  const { authLoading, user } = useAuth();

  useEffect(() => {
    if (authLoading) return;
    if (path === "/" && user) { navigate("/app"); return; }
    if (path === "/app" && !user) { navigate("/login"); return; }
    if ((path === "/login" || path === "/signup" || path === "/reset-password") && user) { navigate("/app"); return; }
  }, [path, user, authLoading, navigate]);

  if (authLoading) {
    return <div style={{ minHeight: "100vh", display: "flex", alignItems: "center", justifyContent: "center", color: "rgba(233,233,237,.5)", fontSize: 13 }}>불러오는 중…</div>;
  }

  if (path === "/") {
    if (user) return null; // /app 으로 리다이렉트 중
    return <LandingScreen navigate={navigate} />;
  }
  if (path === "/login") return <AuthScreen mode="login" navigate={navigate} />;
  if (path === "/signup") return <AuthScreen mode="signup" navigate={navigate} />;
  if (path === "/reset-password") return <AuthScreen mode="reset" navigate={navigate} />;
  if (path === "/app") {
    if (!user) return null;
    return <AppScreen userEmail={user.email} userId={user.uid} onLogout={() => window.EgCalAuth.logout()} />;
  }
  return <NotFoundScreen loggedIn={!!user} navigate={navigate} />;
}

ReactDOM.createRoot(document.getElementById("root")).render(<App />);
