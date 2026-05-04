const http = require('http');
const fs = require('fs');
const path = require('path');

const PORT = 5001;
const GEOJSON_PATH = path.join(__dirname, 'geojson', 'fetched-node.geojson');

const server = http.createServer((req, res) => {
  // CORS headers
  res.setHeader('Access-Control-Allow-Origin', '*');
  res.setHeader('Access-Control-Allow-Methods', 'GET, POST, OPTIONS');
  res.setHeader('Access-Control-Allow-Headers', 'Content-Type');

  if (req.method === 'OPTIONS') {
    res.writeHead(204);
    res.end();
    return;
  }

  // API Endpoint: Save Node
  if (req.method === 'POST' && req.url === '/save-node') {
    let body = '';
    req.on('data', chunk => body += chunk.toString());
    req.on('end', () => {
      try {
        const { lon, lat } = JSON.parse(body);
        console.log(`📍 Saving node: ${lon}, ${lat}`);

        // Read existing file
        let data = { type: "FeatureCollection", features: [] };
        if (fs.existsSync(GEOJSON_PATH)) {
            const content = fs.readFileSync(GEOJSON_PATH, 'utf8');
            if (content.trim()) data = JSON.parse(content);
        }

        // Add new feature
        data.features.push({
          type: "Feature",
          properties: { 
              id: Date.now(), 
              timestamp: new Date().toLocaleString(),
              type: "fetched",
              heading: body.heading || 0
          },
          geometry: { type: "Point", coordinates: [lon, lat] }
        });

        // Save back
        fs.writeFileSync(GEOJSON_PATH, JSON.stringify(data, null, 2));
        
        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ success: true, count: data.features.length }));
      } catch (err) {
        console.error("Save Error:", err);
        res.writeHead(500, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ error: err.message }));
      }
    });
    return;
  }

  // Static File Serving
  // Strip query strings (like ?t=123) from the URL
  const urlPathname = req.url.split('?')[0];
  let urlPath = urlPathname === '/' ? '/index.html' : urlPathname;
  let filePath = path.join(__dirname, urlPath);

  // If path is a directory, look for index.html inside it
  try {
    if (fs.existsSync(filePath) && fs.statSync(filePath).isDirectory()) {
      filePath = path.join(filePath, 'index.html');
    }
  } catch (e) { /* ignore stat errors */ }

  const ext = path.extname(filePath);
  const mimeTypes = {
    '.html': 'text/html',
    '.js': 'text/javascript',
    '.css': 'text/css',
    '.json': 'application/json',
    '.geojson': 'application/json',
    '.png': 'image/png',
    '.jpg': 'image/jpg',
    '.svg': 'image/svg+xml'
  };

  fs.readFile(filePath, (err, content) => {
    if (err) {
      if (err.code === 'ENOENT') {
        res.writeHead(404);
        res.end('404 Not Found');
      } else {
        res.writeHead(500);
        res.end('Internal Server Error: ' + err.code);
      }
    } else {
      res.writeHead(200, { 'Content-Type': mimeTypes[ext] || 'text/plain' });
      res.end(content);
    }
  });
});

server.listen(PORT, '0.0.0.0', () => {
  console.log(`
  🚀 BRIDGE SERVER ACTIVE
  -----------------------------------------
  Local Access:   http://localhost:${PORT}
  Mobile Access:  http://192.168.1.175:${PORT}
  
  Files being served from: ${__dirname}
  Writing nodes to: geojson/fetched-node.geojson
  -----------------------------------------
  `);
});
