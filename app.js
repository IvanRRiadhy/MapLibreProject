// app.js — display-only map with simple 3D extrusions for the indoor plan
// Replace with your own MapTiler key
// const MAPTILER_KEY = "ffyommcZH3MxvLP2KHvR"; // get one at https://cloud.maptiler.com/
// const STYLE_URL = `https://api.maptiler.com/maps/basic-v2/style.json?key=${MAPTILER_KEY}`;

// Data files expected in the same folder (adjust if needed)
// 3D settings (meters)
const START_ICON_DATAURI =
  'data:image/svg+xml;utf8,' +
  encodeURIComponent(`
<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 512 512">
  <defs>
    <linearGradient id="g" x1="0" y1="0" x2="1" y2="1">
      <stop offset="0" stop-color="#87baff"/>
      <stop offset="1" stop-color="#007bff"/>
    </linearGradient>
  </defs>
  <path d="M256 0L480 512 256 384 32 512 256 0z" fill="url(#g)"/>
</svg>`);
const WALL_THICKNESS_M = 0.4;
const WALL_HEIGHT_M = 0.5;

const DOOR_THICKNESS_M = 0.2;
const DOOR_HEIGHT_M = 0;
const FILES = {
  walls: "geojson/floor1-walls.geojson",
  walkable: "geojson/floor1-walkable.geojson",
  doors: "geojson/floor1-doors.geojson",
  portals: "geojson/floor1-portal.geojson",
  pois: "geojson/floor1-poi.geojson",
  navlines: "geojson/floor1-navigationlines2.geojson",
  navpoints: "geojson/floor1-navigationpoints.geojson" // optional, used if present
};
let navPath = [];        // full array of coordinates [lon,lat]
let navIndex = 0;        // current index along the path
let navDirection = 1;    // +1 forward, -1 backward
let navEndCoord = null;
// Smooth-move state
let navCumDist = [];      // cumulative meters per vertex
let navTotalDist = 0;     // total path length (m)
let navDistPos = 0;       // current distance along path (m)

// Key/animation flags
let keyFwd = false, keyBack = false;
let moveDir = 0;          // +1 forward, -1 backward, 0 idle
let isMoving = false;
let lastTs = 0;

// Follow-camera settings (tweak to taste)
const CAM = {
  lookAheadM: 25,            // how far ahead of the marker to show (meters)
  minZoom: 17.5,             // indoor floorplan sweet-spot
  maxZoom: 22,
  easeMs: 120,               // small smoothing per update
  padTop: 80,
  padBottom: 320,            // bigger bottom pad => marker appears lower
  padSide: 120
};

let camZoomSmoothed = null;
let followCamera = true;     // toggle if you ever want to disable


// Motion knobs
const MAX_STEP_PX = 5;          // cap per-frame step in screen pixels
const SPEED_PX_PER_SEC = 160;   // hold speed; tweak to taste

// Small helpers
const rad = (d) => d * Math.PI / 180;
function lonLatToMeters([lon, lat]) {
  // WebMercator projection (meters)
  const x = lon * 20037508.34 / 180;
  const y = Math.log(Math.tan((90 + lat) * Math.PI / 360)) / (Math.PI / 180);
  return [x, y * 20037508.34 / 180];
}
function distMeters(a, b) {
  const [ax, ay] = lonLatToMeters(a);
  const [bx, by] = lonLatToMeters(b);
  const dx = ax - bx, dy = ay - by;
  return Math.sqrt(dx*dx + dy*dy);
}
function fmt(m) { return `${m.toFixed(1)} m`; }

// Graph over existing navigation lines only
class Graph {
  constructor() {
    this.nodes = new Map();  // key: "lon,lat" -> { id, coord:[lon,lat], edges:[{to, w}] }
  }
  _idFromCoord(c) { return `${c[0].toFixed(8)},${c[1].toFixed(8)}`; }

  ensureNode(coord) {
    const id = this._idFromCoord(coord);
    if (!this.nodes.has(id)) {
      this.nodes.set(id, { id, coord, edges: [] });
    }
    return this.nodes.get(id);
  }

  addEdge(aCoord, bCoord) {
    const a = this.ensureNode(aCoord);
    const b = this.ensureNode(bCoord);
    const w = distMeters(a.coord, b.coord);
    a.edges.push({ to: b.id, w });
    b.edges.push({ to: a.id, w }); // undirected
  }

  nearestNodeToCoord(coord) {
    let best = null, bestD = Infinity;
    for (const n of this.nodes.values()) {
      const d = distMeters(coord, n.coord);
      if (d < bestD) { best = n; bestD = d; }
    }
    return { node: best, dist: bestD };
  }

  dijkstra(fromId, toId) {
    const distMap = new Map();
    const prev = new Map();
    const visited = new Set();

    for (const id of this.nodes.keys()) distMap.set(id, Infinity);
    distMap.set(fromId, 0);

    // simple priority queue via array (graph is small/indoor)
    const pq = [{ id: fromId, d: 0 }];

    while (pq.length) {
      // extract-min
      pq.sort((a, b) => a.d - b.d);
      const { id } = pq.shift();
      if (visited.has(id)) continue;
      visited.add(id);
      if (id === toId) break;

      const u = this.nodes.get(id);
      for (const e of u.edges) {
        if (visited.has(e.to)) continue;
        const alt = distMap.get(id) + e.w;
        if (alt < distMap.get(e.to)) {
          distMap.set(e.to, alt);
          prev.set(e.to, id);
          pq.push({ id: e.to, d: alt });
        }
      }
    }

    if (!prev.has(toId) && fromId !== toId) return { coords: [], length: 0 };

    const pathIds = [];
    let cur = toId;
    pathIds.push(cur);
    while (prev.has(cur)) {
      cur = prev.get(cur);
      pathIds.push(cur);
    }
    pathIds.reverse();
    const coords = pathIds.map(id => this.nodes.get(id).coord);
    const length = coords.reduce((acc, c, i) => i ? acc + distMeters(coords[i-1], c) : 0, 0);
    return { coords, length };
  }
}
function emptyFC() {
  return { type: 'FeatureCollection', features: [] };
}


(async function main() {
  function metersPerPixelAtLat(lat, zoom) {
  // WebMercator m/px approximation
  return 156543.03392 * Math.cos(lat * Math.PI / 180) / Math.pow(2, zoom);
}

function buildCumDistances(coords) {
  const cum = [0];
  for (let i = 1; i < coords.length; i++) {
    cum[i] = cum[i - 1] + distMeters(coords[i - 1], coords[i]);
  }
  return { cum, total: cum[cum.length - 1] || 0 };
}

function metersToLonLat([x, y]) {
  const lon = x * 180 / 20037508.34;
  const lat = (180 / Math.PI) * (2 * Math.atan(Math.exp(y * Math.PI / 20037508.34)) - Math.PI / 2);
  return [lon, lat];
}

// Interpolate along the path at distance d (meters)
function coordAtDistance(path, cum, d) {
  d = Math.max(0, Math.min(d, cum[cum.length - 1] || 0));
  if (path.length === 0) return { coord: null, idx: 0 };
  if (path.length === 1) return { coord: path[0], idx: 0 };

  // find segment
  let i = 0;
  while (i < cum.length - 1 && cum[i + 1] < d) i++;

  const segLen = (cum[i + 1] - cum[i]) || 1e-9;
  const t = (d - cum[i]) / segLen;

  // interpolate in meters, then convert back to lon/lat
  const p0m = lonLatToMeters(path[i]);
  const p1m = lonLatToMeters(path[i + 1]);
  const xm = p0m[0] + t * (p1m[0] - p0m[0]);
  const ym = p0m[1] + t * (p1m[1] - p0m[1]);
  return { coord: metersToLonLat([xm, ym]), idx: i };
}

function clamp(v, a, b) { return Math.max(a, Math.min(b, v)); }

function norm180(a){ return ((a + 180) % 360 + 360) % 360 - 180; }
function shortestTo(from, to){
  from = norm180(from); to = norm180(to);
  return from + norm180(to - from); // minimal delta
}

function norm180(a){ return ((a + 180) % 360 + 360) % 360 - 180; }
function shortestTo(from, to){
  from = norm180(from); to = norm180(to);
  return from + norm180(to - from);
}

function updateNavCamera(pos, ahead, headingDeg) {
  if (!followCamera || !pos || !ahead) return;

  // Use bounds solely to compute a good zoom for the look-ahead slice
  const bounds = new maplibregl.LngLatBounds(
    new maplibregl.LngLat(pos[0], pos[1]),
    new maplibregl.LngLat(ahead[0], ahead[1])
  );
  const camNoPad = map.cameraForBounds(bounds, { maxZoom: CAM.maxZoom }); // no extra padding here
  if (!camNoPad) return;

  const targetZoom = clamp(camNoPad.zoom, CAM.minZoom, CAM.maxZoom);
  if (camZoomSmoothed == null) camZoomSmoothed = targetZoom;
  camZoomSmoothed = 0.85 * camZoomSmoothed + 0.15 * targetZoom;

  // Rotate with the marker (you already flipped the sign earlier)
  const desiredBearing = headingDeg;
  const easedBearing = shortestTo(map.getBearing(), desiredBearing);

  map.easeTo({
    center: pos,                 // ← anchor camera on the marker
    zoom: camZoomSmoothed,       // ← zoom chosen to fit the look-ahead slice
    bearing: easedBearing,
    pitch: map.getPitch(),
    duration: CAM.easeMs
  });
}



  // Build map (2D style to avoid 3D blockage)
  const map = new maplibregl.Map({
    container: "map",
    style: `https://api.maptiler.com/maps/openstreetmap/style.json?key=${MAPTILER_KEY}`,
  center: [106.8272, -6.1754],
  zoom: 18,
  pitch: 55,          // << give some tilt
  bearing: -15,       // << slight angle helps depth perception
  attributionControl: false
  });
  map.addControl(new maplibregl.NavigationControl({ showCompass: false }), "top-right");
  map.addControl(new maplibregl.AttributionControl({ compact: true }));

  // Load data
  const load = (f) => fetch(f).then(r => r.json());
  const [
    walls, walkable, doors, portals, pois, navlines, navpointsMaybe
  ] = await Promise.all([
    load(FILES.walls),
    load(FILES.walkable),
    load(FILES.doors),
    load(FILES.portals),
    load(FILES.pois),
    load(FILES.navlines),
    load(FILES.navpoints).catch(() => null)
  ]);
// Build extrudable polygons from a FeatureCollection that may mix
// LineString/MultiLineString and Polygon/MultiPolygon.
function toExtrudable(fc, thicknessMeters) {
  const out = { type: "FeatureCollection", features: [] };

  for (const f of fc.features ?? []) {
    const g = f.geometry;
    if (!g) continue;

    // 1) Keep polygons as-is (clone & keep props)
    if (/Polygon$/.test(g.type)) {
      const clone = JSON.parse(JSON.stringify(f));
      out.features.push(clone);
      continue;
    }

    // 2) Buffer linework (per feature) into thin polygons
    if (g.type === "LineString" || g.type === "MultiLineString") {
      try {
        // Buffer returns a FeatureCollection or Feature (Polygon)
        const buff = turf.buffer(f, thicknessMeters, { units: "meters" });
        if (buff?.type === "FeatureCollection") {
          for (const bf of buff.features ?? []) {
            if (/Polygon$/.test(bf.geometry?.type || "")) {
              // carry over original properties too
              bf.properties = { ...(f.properties || {}), ...(bf.properties || {}) };
              out.features.push(bf);
            }
          }
        } else if (buff?.type === "Feature" && /Polygon$/.test(buff.geometry?.type || "")) {
          buff.properties = { ...(f.properties || {}), ...(buff.properties || {}) };
          out.features.push(buff);
        }
      } catch (e) {
        console.warn("Buffer failed for a wall/door feature:", e, f);
      }
      continue;
    }

    // 3) Ignore other geometry types
  }

  return out;
}


const walls3d = toExtrudable(walls, WALL_THICKNESS_M);
walls3d.features.forEach(f => {
  f.properties = { ...(f.properties || {}), height: WALL_HEIGHT_M };
});

const doors3d = toExtrudable(doors, DOOR_THICKNESS_M);
doors3d.features.forEach(f => {
  f.properties = { ...(f.properties || {}), height: DOOR_HEIGHT_M };
});

  // Fit initial view to walkable (if present)
  function fitTo(fc) {
    if (!fc || !fc.features || !fc.features.length) return;
    const bbox = computeBbox(fc);
    map.fitBounds(bbox, { padding: 60, duration: 0 });
  }
  function computeBbox(fc) {
    let minX=Infinity,minY=Infinity,maxX=-Infinity,maxY=-Infinity;
    for (const f of fc.features) {
      const geom = f.geometry;
      const eachCoord = (c) => { minX=Math.min(minX,c[0]); minY=Math.min(minY,c[1]); maxX=Math.max(maxX,c[0]); maxY=Math.max(maxY,c[1]); };
      if (geom.type === "Point") eachCoord(geom.coordinates);
      else if (geom.type === "LineString") geom.coordinates.forEach(eachCoord);
      else if (geom.type === "Polygon") geom.coordinates.flat().forEach(eachCoord);
      else if (geom.type === "MultiLineString") geom.coordinates.flat().forEach(eachCoord);
      else if (geom.type === "MultiPolygon") geom.coordinates.flat(2).forEach(eachCoord);
      else if (geom.type === "MultiPoint") geom.coordinates.forEach(eachCoord);
    }
    return [[minX, minY],[maxX, maxY]];
  }
function orientCameraForRoute(start, end) {
  if (!start || !end) return;
  if (start[0] === end[0] && start[1] === end[1]) return;

  const segBearing = turf.bearing(turf.point(start), turf.point(end));
  const targetBearing = -segBearing; // so the line points "up"

  const bounds = new maplibregl.LngLatBounds(
    new maplibregl.LngLat(start[0], start[1]),
    new maplibregl.LngLat(end[0], end[1])
  );

  const cam = map.cameraForBounds(bounds, {
    padding: { top: 100, right: 140, bottom: 320, left: 140 }, // start lower, end higher
    maxZoom: 22
  });
  if (!cam || !isFinite(cam.zoom)) return;

  map.stop();
  map.easeTo({
    center: cam.center,
    zoom: cam.zoom,
    bearing: targetBearing,
    pitch: map.getPitch(),   // keep your current tilt
    duration: 800
  });
}



  // Build routing graph from navlines (strictly follow given segments)
  const graph = new Graph();
  for (const feat of navlines.features) {
    if (!feat.geometry || feat.geometry.type !== "LineString") continue;
    const coords = feat.geometry.coordinates;
    for (let i = 1; i < coords.length; i++) {
      graph.addEdge(coords[i-1], coords[i]);
    }
  }

  // Prepare POI options
  const poiItems = pois.features
    .filter(f => f.geometry?.type === "Point")
    .map((f, idx) => {
      const props = f.properties || {};
      const name = props.name || props.label || props.id || `POI-${idx+1}`;
      return { id: props.id ?? name, name, coord: f.geometry.coordinates };
    })
    .sort((a,b) => a.name.localeCompare(b.name));

  // UI wiring
  const startSel = document.getElementById("startPoi");
  const endSel = document.getElementById("endPoi");
  const goBtn = document.getElementById("goBtn");
  const clearBtn = document.getElementById("clearBtn");
  const statusNote = document.getElementById("statusNote");

  function fillSelect(el, items) {
    el.innerHTML = "";
    const opt0 = document.createElement("option");
    opt0.value = "";
    opt0.textContent = "-- select --";
    el.appendChild(opt0);
    for (const it of items) {
      const o = document.createElement("option");
      o.value = it.id;
      o.textContent = it.name;
      el.appendChild(o);
    }
  }
  fillSelect(startSel, poiItems);
  fillSelect(endSel, poiItems);

  goBtn.addEventListener("click", () => {
    const sId = startSel.value;
    const eId = endSel.value;
    if (!sId || !eId) {
      status("Pick both start and end.");
      return;
    }
    if (sId === eId) {
      status("Start and end are the same.");
      drawRoute({ coords: [], length: 0 });
      return;
    }

    const sPoi = poiItems.find(p => p.id == sId);
    const ePoi = poiItems.find(p => p.id == eId);
    if (!sPoi || !ePoi) {
      status("Invalid POI selection.");
      return;
    }

    // Snap POIs to nearest *existing* nav node — no new lines
    const { node: sNode, dist: sDist } = graph.nearestNodeToCoord(sPoi.coord);
    const { node: eNode, dist: eDist } = graph.nearestNodeToCoord(ePoi.coord);

    // Optional: enforce a maximum snap distance to avoid silly jumps
    const MAX_SNAP_METERS = 20; // tweak as needed (indoor tolerance)
    if (!sNode || !eNode) {
      status("No navigation nodes found.");
      drawRoute({ coords: [], length: 0 });
      return;
    }
    if (sDist > MAX_SNAP_METERS || eDist > MAX_SNAP_METERS) {
      status(`POI too far from nav lines (start: ${fmt(sDist)}, end: ${fmt(eDist)}).`);
      drawRoute({ coords: [], length: 0 });
      return;
    }

    const path = graph.dijkstra(sNode.id, eNode.id);
    // updateNavMarkers(sPoi.coord, ePoi.coord, path.coords);
//     if (path.coords.length) {
//   updateStartMarker(path.coords[0], path.coords);
// }
    if (!path.coords.length) {
      status("No path found using existing navigation lines.");
    } else {
      status(`Path length: ${fmt(path.length)} (snapped: S ${fmt(sDist)}, E ${fmt(eDist)})`);
    }
    drawRoute(path);

    // Fit to route if available
    // if (path.coords.length) {
    //   const fc = { type: "FeatureCollection", features: [{ type: "Feature", geometry: { type: "LineString", coordinates: path.coords }, properties: {} }] };
    //   map.fitBounds(computeBbox(fc), { padding: 60, duration: 300 });
    // }
// init nav controller + markers
if (path.coords.length) {
  navPath = path.coords;
  navIndex = 0;                 // (kept but unused for smooth mode)
  navDirection = 1;
  navEndCoord = path.coords[path.coords.length - 1];

  // NEW: precompute cumulative distances
  const out = buildCumDistances(navPath);
  navCumDist = out.cum;
  navTotalDist = out.total;
  navDistPos = 0;               // start at path origin

updateNavMarkers(navPath[0], navEndCoord, navPath);

// Use the marker’s first segment for heading
const pos0 = navPath[0];
const pos1 = navPath[1] ?? navPath[0];
const heading0 = turf.bearing(turf.point(pos0), turf.point(pos1));

// look-ahead target for bottom-center framing
const ahead0 = coordAtDistance(
  navPath,
  navCumDist,
  Math.min(CAM.lookAheadM, navTotalDist)
).coord || pos0;

// snap the camera to marker heading
updateNavCamera(pos0, ahead0, heading0);
}
  });

clearBtn.addEventListener("click", () => {
  drawRoute({ coords: [], length: 0 });
  const src = map.getSource('nav-markers');
  if (src) src.setData({ type: 'FeatureCollection', features: [] });
  status("");
});

  function status(msg) { statusNote.textContent = msg || ""; }
function updateNavMarkers(startLonLat, endLonLat, pathCoords) {
  // Bearing: from first segment of the route (fallback 0)
  let bearing = 0;
  if (Array.isArray(pathCoords) && pathCoords.length >= 2) {
    // turf expects [lon,lat]
    bearing = turf.bearing(
      turf.point(pathCoords[0]),
      turf.point(pathCoords[1])
    );
  }

  const fc = {
    type: 'FeatureCollection',
    features: [
      {
        type: 'Feature',
        properties: { role: 'start', bearing },
        geometry: { type: 'Point', coordinates: startLonLat }
      },
      {
        type: 'Feature',
        properties: { role: 'end' },
        geometry: { type: 'Point', coordinates: endLonLat }
      }
    ]
  };

  const src = map.getSource('nav-markers');
  if (src) src.setData(fc);
}


function updateStartMarker(coord, pathCoords) {
  let bearing = 0;
  if (Array.isArray(pathCoords) && pathCoords.length >= 2) {
    const from = turf.point(pathCoords[0]);
    const to   = turf.point(pathCoords[1]);
    bearing = turf.bearing(from, to);
  }

  const fc = {
    type: 'FeatureCollection',
    features: [
      {
        type: 'Feature',
        properties: { role: 'start', bearing },
        geometry: { type: 'Point', coordinates: coord }
      }
    ]
  };
  const src = map.getSource('nav-markers');
  if (src) src.setData(fc);
}



  // Add sources/layers when style is ready
  map.on("load", () => {


    map.loadImage('assets/arrow.png', (error, image) => {
  if (error) throw error;
  if (!map.hasImage('start-icon')) {
    map.addImage('start-icon', image);
  }
});
    console.log("walls3d sample:", walls3d.features[0]?.geometry?.type, walls3d);
console.log("doors3d sample:", doors3d.features[0]?.geometry?.type, doors3d);
    // Sources
    map.addSource("walkable", { type: "geojson", data: walkable });
    map.addSource("walls-3d", { type: "geojson", data: walls3d });
map.addSource("doors-3d", { type: "geojson", data: doors3d });
    map.addSource("portals", { type: "geojson", data: portals });
    map.addSource("pois", { type: "geojson", data: pois });
    map.addSource("navlines", { type: "geojson", data: navlines });
    map.addSource("route", { type: "geojson", data: emptyLine() });

    // Layers
    map.addLayer({
      id: "walkable-fill",
      type: "fill",
      source: "walkable",
      paint: { "fill-color": "#29a329", "fill-opacity": 0.15 }
    });

map.addLayer({
  id: "walls-3d-extrusion",
  type: "fill-extrusion",
  source: "walls-3d",
  paint: {
    "fill-extrusion-color": "#b0b0b0",
    "fill-extrusion-height": ["coalesce", ["to-number", ["get", "height"]], WALL_HEIGHT_M],
    "fill-extrusion-opacity": 0.95
  }
});

map.addLayer({
  id: "doors-3d-extrusion",
  type: "fill-extrusion",
  source: "doors-3d",
  paint: {
    "fill-extrusion-color": "#5c9ded",
    "fill-extrusion-height": ["coalesce", ["to-number", ["get", "height"]], DOOR_HEIGHT_M],
    "fill-extrusion-opacity": 0.9
  }
});

    map.addLayer({
      id: "portals-circle",
      type: "circle",
      source: "portals",
      paint: { "circle-radius": 4, "circle-color": "#ffd166", "circle-stroke-color": "#8a6d00", "circle-stroke-width": 1 }
    });

    map.addLayer({
      id: "pois-circle",
      type: "circle",
      source: "pois",
      paint: { "circle-radius": 5, "circle-color": "#ff6b6b", "circle-stroke-color": "#7a1f1f", "circle-stroke-width": 1 }
    });

    map.addLayer({
      id: "pois-label",
      type: "symbol",
      source: "pois",
      layout: {
        "text-field": ["get", "name"],
        "text-size": 12,
        "text-offset": [0, 1],
        "text-anchor": "top"
      },
      paint: { "text-color": "#ffffff", "text-halo-color": "#000", "text-halo-width": 1 }
    });

    map.addLayer({
      id: "navlines-line",
      type: "line",
      source: "navlines",
      paint: { "line-color": "transparent", "line-width": 2 }
    });

    map.addLayer({
      id: "route-line",
      type: "line",
      source: "route",
      paint: { "line-color": "#00d1b2", "line-width": 6 }
    });

    fitTo(walkable ?? walls ?? navlines);

    // 2a) Register the start icon
(function addStartIcon() {
  const img = new Image(128, 128);
  img.onload = () => {
    if (!map.hasImage('start-arrow')) map.addImage('start-arrow', img);
  };
  img.src = START_ICON_DATAURI;  // or 'assets/start.png'
})();

// 2b) Add a source for nav markers (start/end)
map.addSource('nav-markers', {
  type: 'geojson',
  data: { type: 'FeatureCollection', features: [] }
});
// 2c) Start icon layer (rotates with bearing)
map.addLayer({
  id: 'nav-start',
  type: 'symbol',
  source: 'nav-markers',
  filter: ['==', ['get', 'role'], 'start'],
  layout: {
    'icon-image': 'start-icon',
    'icon-size': 0.07,
    'icon-anchor': 'bottom',
    'icon-rotate': ['get', 'bearing'],    // << rotate with path
    'icon-rotation-alignment': 'map',     // rotate relative to map
    'icon-allow-overlap': true
  }
});

// 2d) (Optional) end marker as a circle
map.addLayer({
  id: 'nav-end-circle',
  type: 'circle',
  source: 'nav-markers',
  filter: ['==', ['get', 'role'], 'end'],
  paint: {
    'circle-radius': 6,
    'circle-color': '#ff6b6b',
    'circle-stroke-color': '#7a1f1f',
    'circle-stroke-width': 1
  }
});
  map.setPadding({
    top: CAM.padTop,
    right: CAM.padSide,
    bottom: CAM.padBottom,   // pushes the visual center upward
    left: CAM.padSide
  });
      map.getCanvas().setAttribute('tabindex', '0');
  map.getCanvas().focus();
  });

  function emptyLine() {
    return { type: "FeatureCollection", features: [{
      type: "Feature", properties: {}, geometry: { type: "LineString", coordinates: [] }
    }]};
  }

  function drawRoute(result) {
    const src = map.getSource("route");
    if (!src) return;
    const data = emptyLine();
    data.features[0].geometry.coordinates = result.coords || [];
    src.setData(data);
  }

  // ---- Modal + reset helpers (hoisted function declarations) ----
function resetNavigation() {
  // stop motion
  isMoving = false; keyFwd = false; keyBack = false; moveDir = 0; lastTs = 0;

  // clear state
  navPath = []; navIndex = 0; navDirection = 1; navEndCoord = null;
  navCumDist = []; navTotalDist = 0; navDistPos = 0;

  // clear layers
  map.getSource('nav-markers')?.setData({ type:'FeatureCollection', features:[] });
  map.getSource('route')?.setData(emptyLine());

  // reset dropdowns + status
  const startSel = document.getElementById("startPoi");
  const endSel = document.getElementById("endPoi");
  const statusNote = document.getElementById("statusNote");
  if (startSel) startSel.value = "";
  if (endSel) endSel.value = "";
  if (statusNote) statusNote.textContent = "";
}

function showDoneModal() {
  const modal = document.getElementById('doneModal');
  const okBtn = document.getElementById('doneOk');
  if (!modal || !okBtn) { alert('Navigation is done'); resetNavigation(); return; }
  modal.classList.remove('hidden');
  resetNavigation(); // clear route/markers while modal is up
  setTimeout(() => okBtn.focus(), 0);
}
function hideDoneModal() {
  const modal = document.getElementById('doneModal');
  if (modal) modal.classList.add('hidden');
}

// wire modal buttons/keys (once)
document.getElementById('doneOk')?.addEventListener('click', hideDoneModal);
document.getElementById('doneModal')?.addEventListener('click', (e) => {
  if (e.target.id === 'doneModal') hideDoneModal();
});
document.addEventListener('keydown', (e) => {
  const modal = document.getElementById('doneModal');
  if (!modal || modal.classList.contains('hidden')) return;
  if (e.key === 'Escape' || e.key === 'Enter') hideDoneModal();
});
// ---- end modal helpers ----



function animateMove(ts) {
  if (!isMoving || !navPath.length || !navCumDist.length) { lastTs = 0; return; }
  if (!lastTs) lastTs = ts;
  const dt = (ts - lastTs) / 1000;
  lastTs = ts;

  // desired pixel step for this frame
  const stepPx = Math.min(MAX_STEP_PX, SPEED_PX_PER_SEC * dt);

  // convert px → meters at current zoom/lat
  const here = coordAtDistance(navPath, navCumDist, navDistPos).coord || navPath[0];
  const mpp = metersPerPixelAtLat(here[1], map.getZoom());
  const stepMeters = stepPx * mpp;

  // advance along the path
  navDistPos += moveDir * stepMeters;
  navDistPos = Math.max(0, Math.min(navTotalDist, navDistPos));

  // place/rotate the marker
  const pos = coordAtDistance(navPath, navCumDist, navDistPos).coord;
  const probe = Math.min(stepMeters * 2, 1); // small lookahead for bearing
  const ahead = coordAtDistance(
    navPath,
    navCumDist,
    navDistPos + (moveDir >= 0 ? probe : -probe)
  ).coord || pos;

  const bearing = turf.bearing(turf.point(pos), turf.point(ahead));
  const features = [{
    type: 'Feature',
    properties: { role: 'start', bearing },
    geometry: { type: 'Point', coordinates: pos }
  }];
  if (navEndCoord) {
    features.push({
      type: 'Feature',
      properties: { role: 'end' },
      geometry: { type: 'Point', coordinates: navEndCoord }
    });
  }
  map.getSource('nav-markers')?.setData({ type: 'FeatureCollection', features });
updateNavCamera(pos, ahead, bearing);
  // done?
  if (moveDir === 1 && Math.abs(navTotalDist - navDistPos) < 0.01) {
    isMoving = false;
    showDoneModal(); // also resets nav
    return;
  }

  // continue
  requestAnimationFrame(animateMove);
}

document.addEventListener('keydown', (e) => {
  if (!navPath.length) return;
  if (e.key === 'w' || e.key === 'ArrowUp') {
    e.preventDefault(); keyFwd = true;
  } else if (e.key === 's' || e.key === 'ArrowDown') {
    e.preventDefault(); keyBack = true;
  } else { return; }

  // compute direction and (re)start animation if needed
  moveDir = keyFwd ? 1 : (keyBack ? -1 : 0);
  if (moveDir !== 0 && !isMoving) {
    isMoving = true; lastTs = 0;
    requestAnimationFrame(animateMove);
  }
});

document.addEventListener('keyup', (e) => {
  if (e.key === 'w' || e.key === 'ArrowUp') keyFwd = false;
  else if (e.key === 's' || e.key === 'ArrowDown') keyBack = false;
  else return;

  moveDir = keyFwd ? 1 : (keyBack ? -1 : 0);
  if (moveDir === 0) isMoving = false;
});


})();


