// 로컬 개발 서버 — http://localhost:8080
// Node 내장 모듈만 사용 (별도 설치 불필요). 실행: node server.js
const http = require("http");
const fs = require("fs");
const path = require("path");

const PORT = 8080;
const ROOT = __dirname;
const MIME = {
  ".html": "text/html; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".css": "text/css; charset=utf-8",
  ".json": "application/json; charset=utf-8",
  ".svg": "image/svg+xml",
  ".png": "image/png",
};

function serveFile(filePath, res) {
  const ext = path.extname(filePath);
  res.writeHead(200, { "Content-Type": MIME[ext] || "application/octet-stream" });
  fs.createReadStream(filePath).pipe(res);
}

http.createServer((req, res) => {
  const urlPath = decodeURIComponent((req.url || "/").split("?")[0]);
  const filePath = path.join(ROOT, urlPath === "/" ? "/index.html" : urlPath);

  fs.stat(filePath, (err, stat) => {
    if (!err && stat.isFile()) { serveFile(filePath, res); return; }
    // 클라이언트 라우팅(/login, /app 등)은 확장자가 없으므로 index.html로 폴백
    if (!path.extname(urlPath)) { serveFile(path.join(ROOT, "index.html"), res); return; }
    res.writeHead(404, { "Content-Type": "text/plain; charset=utf-8" });
    res.end("Not found");
  });
}).listen(PORT, () => {
  console.log(`Eg-Cal 개발 서버: http://localhost:${PORT}`);
});
