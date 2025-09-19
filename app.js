// app.js — Indoor navigation with 3D walls/doors and room highlighting

// Replace with your MapTiler key

// Settings
const WALL_THICKNESS_M = 0.4;
const DOOR_THICKNESS_M = 0.2;

const START_ICON_DATAURI =
  'data:image/svg+xml;utf8,' +
  encodeURIComponent(`
<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 512 512">
  <path d="M256 0L480 512 256 384 32 512 256 0z" fill="#007bff"/>
</svg>`);

const FLOORS = {
  LT1: {
    walls: "geojson/RSUP-LT1-Walls.geojson",
    walkable: "geojson/RSUP-LT1-Walkable.geojson",
    doors: "geojson/RSUP-LT1-Doors.geojson",
    rooms: "geojson/RSUP-LT1-Rooms.geojson",
    pois: "geojson/RSUP-POIs.geojson", // combined POIs
    navlines: "geojson/RSUP-NavLines.geojson"
  },
  LT2: {
    walls: "geojson/RSUP-Walls.geojson",
    walkable: "geojson/RSUP-Walkable.geojson",
    doors: "geojson/RSUP-Doors.geojson",
    rooms: "geojson/RSUP-Rooms.geojson",
    pois: "geojson/RSUP-POIs.geojson",
    navlines: "geojson/RSUP-NavLines.geojson"
  }
};

let currentFloor = "LT2";

const FILES = {
  walls: "geojson/RSUP-Walls.geojson",
  walkable: "geojson/RSUP-Walkable.geojson",
  doors: "geojson/RSUP-Doors.geojson",
  pois: "geojson/RSUP-POIs.geojson",   // includes rooms + stairs
  navlines: "geojson/RSUP-NavLines.geojson",
  rooms: "geojson/RSUP-Rooms.geojson"
};

// Navigation state
let navPath = [];
let navEndCoord = null;
let navCumDist = [];
let navTotalDist = 0;
let navDistPos = 0;

let keyFwd = false;
let keyBack = false;
let moveDir = 0;
let isMoving = false;
let lastTs = 0;

// Camera settings
const CAM = {
  lookAheadM: 25,
  minZoom: 17.5,
  maxZoom: 22,
  easeMs: 120,
  padTop: 80,
  padBottom: 320,
  padSide: 120
};

let camZoomSmoothed = null;
let followCamera = true;

// Motion
const MAX_STEP_PX = 5;
const SPEED_PX_PER_SEC = 160;

// Helpers

function lonLatToMeters([lon, lat]) {
  const x = lon * 20037508.34 / 180;
  const y = Math.log(Math.tan((90 + lat) * Math.PI / 360)) / (Math.PI / 180);
  return [x, y * 20037508.34 / 180];
}
function distMeters(a, b) {
  const [ax, ay] = lonLatToMeters(a);
  const [bx, by] = lonLatToMeters(b);
  return Math.hypot(ax - bx, ay - by);
}
function fmt(m) { return `${m.toFixed(1)} m`; }
function buildCumDistances(coords) {
  const cum = [0];
  for (let i = 1; i < coords.length; i++) cum[i] = cum[i-1] + distMeters(coords[i-1], coords[i]);
  return { cum, total: cum[cum.length-1] || 0 };
}
function coordAtDistance(path, cum, d) {
  d = Math.max(0, Math.min(d, cum[cum.length - 1] || 0));
  if (path.length <= 1) return { coord: path[0], idx: 0 };
  let i = 0; while (i < cum.length - 1 && cum[i+1] < d) i++;
  const segLen = (cum[i+1] - cum[i]) || 1e-9;
  const t = (d - cum[i]) / segLen;
  const p0m = lonLatToMeters(path[i]), p1m = lonLatToMeters(path[i+1]);
  return { coord: metersToLonLat([p0m[0] + t*(p1m[0]-p0m[0]), p0m[1] + t*(p1m[1]-p0m[1])]), idx:i };
}
function metersToLonLat([x, y]) {
  const lon = x * 180 / 20037508.34;
  const lat = (180/Math.PI)*(2*Math.atan(Math.exp(y*Math.PI/20037508.34))-Math.PI/2);
  return [lon, lat];
}

function filterPoisByFloor(pois, floorKey) {
  const prefix = floorKey === "LT1" ? "1" : "2";
  return {
    type: "FeatureCollection",
    features: pois.features.filter(f => {
      const id = String(f.properties?.id || "");
      return id.startsWith(prefix);
    })
  };
}

class Graph {
  constructor(){this.nodes=new Map();}
  _idFromCoord(c){return `${c[0].toFixed(8)},${c[1].toFixed(8)}`;}
  ensureNode(coord){const id=this._idFromCoord(coord);if(!this.nodes.has(id))this.nodes.set(id,{id,coord,edges:[]});return this.nodes.get(id);}
  addEdge(aCoord,bCoord){const a=this.ensureNode(aCoord),b=this.ensureNode(bCoord);const w=distMeters(a.coord,b.coord);a.edges.push({to:b.id,w});b.edges.push({to:a.id,w});}
  nearestNodeToCoord(coord){let best=null,bestD=Infinity;for(const n of this.nodes.values()){const d=distMeters(coord,n.coord);if(d<bestD){best=n;bestD=d;}}return {node:best,dist:bestD};}
  dijkstra(fromId,toId){
    const distMap=new Map(),
    prev=new Map(),
    visited=new Set();
    for(const id of this.nodes.keys())
      distMap.set(id,Infinity);distMap.set(fromId,0);
    const pq=[{id:fromId,d:0}];
    while(pq.length){pq.sort((a,b)=>a.d-b.d);
      const {id}=pq.shift();
      if(visited.has(id))continue;
      visited.add(id);
      if(id===toId)break;
      for(const e of this.nodes.get(id).edges){
        if(visited.has(e.to))continue;
        const alt=distMap.get(id)+e.w;
        if(alt<distMap.get(e.to)){
          distMap.set(e.to,alt);
          prev.set(e.to,id);
          pq.push({id:e.to,d:alt});
        }
      }
    }
    if(!prev.has(toId)&&fromId!==toId)
      return{coords:[],length:0};
    const pathIds=[];
    let cur=toId;
    pathIds.push(cur);
    while(prev.has(cur)){
      cur=prev.get(cur);
      pathIds.push(cur);
    }
    pathIds.reverse();
    const coords=pathIds.map(id=>this.nodes.get(id).coord);
    const length=coords.reduce((a,c,i)=>i?a+distMeters(coords[i-1],c):0,0);
    return{coords,length};
  }
}

function emptyFC(){return {type:"FeatureCollection",features:[]};}



function toExtrudable(fc, thicknessMeters) {
  const out = { type: "FeatureCollection", features: [] };
  for (const f of fc.features ?? []) {
    const g = f.geometry;
    if (!g) continue;
    if (/Polygon$/.test(g.type)) {
      const clone = JSON.parse(JSON.stringify(f));
      out.features.push(clone);
      continue;
    }
    if (g.type === "LineString" || g.type === "MultiLineString") {
      try {
        const buff = turf.buffer(f, thicknessMeters, { units: "meters" });
        if (buff?.type === "FeatureCollection") {
          for (const bf of buff.features ?? []) {
            if (/Polygon$/.test(bf.geometry?.type || "")) {
              bf.properties = { ...(f.properties || {}), ...(bf.properties || {}) };
              out.features.push(bf);
            }
          }
        } else if (buff?.type === "Feature" && /Polygon$/.test(buff.geometry?.type || "")) {
          buff.properties = { ...(f.properties || {}), ...(buff.properties || {}) };
          out.features.push(buff);
        }
      } catch (e) {
        console.warn("Buffer failed for wall/door feature:", e, f);
      }
    }
  }
  return out;
}





// ----------------------------------------------------
// MAIN
// ----------------------------------------------------
(async function main() {
  const load = f => fetch(f).then(r => r.json());

  const [walls, walkable, doors, pois, navlines, rooms] =
    await Promise.all([
      load(FILES.walls),
      load(FILES.walkable),
      load(FILES.doors),
      load(FILES.pois),
      load(FILES.navlines),
      load(FILES.rooms)
    ]);

  // Convert to extrudable 3D
  const walls3d = toExtrudable(walls, WALL_THICKNESS_M);
  walls3d.features.forEach(f => {
    f.properties = { ...(f.properties || {}), height: 1 };
  });

  const doors3d = toExtrudable(doors, DOOR_THICKNESS_M);
  doors3d.features.forEach(f => {
    f.properties = { ...(f.properties || {}), height: 0 };
  });

  // Map
  const map = new maplibregl.Map({
    container: "map",
    style: `https://api.maptiler.com/maps/openstreetmap/style.json?key=${MAPTILER_KEY}`,
    center: [106.8272, -6.1754],
    zoom: 18,
    pitch: 55,
    bearing: -15,
    attributionControl: false,
    minZoom: 0,
    maxZoom: 24
  });

  window._map = map;


  map.addControl(new maplibregl.NavigationControl({ showCompass: false }), "top-right");
  map.addControl(new maplibregl.AttributionControl({ compact: true }));

  // Build routing graph
  const graph = new Graph();
  for (const feat of navlines.features) {
    if (!feat.geometry) continue;
    const g = feat.geometry;

    if (g.type === "LineString") {
      const coords = g.coordinates;
      for (let i = 1; i < coords.length; i++) {
        graph.addEdge(coords[i - 1], coords[i]);
      }
    }

    if (g.type === "MultiLineString") {
      for (const line of g.coordinates) {
        for (let i = 1; i < line.length; i++) {
          graph.addEdge(line[i - 1], line[i]);
        }
      }
    }
  }

  // POIs
  const poiItems = pois.features
    .filter(f => f.geometry?.type === "Point")
    .map((f, i) => ({
      id: f.properties?.id ?? `POI-${i + 1}`,
      name: f.properties?.name ?? `POI-${i + 1}`,
      type: f.properties?.type ?? "poi",
      coord: f.geometry.coordinates
    }));

  // UI dropdowns
  const startSel = document.getElementById("startPoi");
  const endSel = document.getElementById("endPoi");

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

  // ----------------------------------------------------
  // Navigation button handlers
  // ----------------------------------------------------
// Store multi-floor navigation state
let segmentPaths = { floor1: [], floor2: [] };
let targetFloor = null;
let currentSegment = 1;
let stairStartCoord = null;
let stairEndCoord = null;

document.getElementById("goBtn").addEventListener("click", async () => {
  const sPoi = poiItems.find(p => p.id == "201"); // always Wayfinding 1
  const ePoi = poiItems.find(p => p.id == endSel.value);

  if (!sPoi) return setStatus("Start POI not found (Waypoint 1 missing)");
  if (!ePoi) return setStatus("Please select a destination");

  const startFloor = String(sPoi.id).charAt(0);
  const endFloor   = String(ePoi.id).charAt(0);

  // ✅ Same floor
  if (startFloor === endFloor) {
    const { node: sNode } = graph.nearestNodeToCoord(sPoi.coord);
    const { node: eNode } = graph.nearestNodeToCoord(ePoi.coord);
    if (!sNode || !eNode) return setStatus("No navigation nodes found");

    const path = graph.dijkstra(sNode.id, eNode.id);
    if (!path.coords.length) return setStatus("No path found");

    drawFullRoute(path.coords, ePoi, rooms);
    return;
  }

  // 🔄 Cross-floor navigation
  // 1. Nearest stair on start floor
  const stairsStart = poiItems.filter(p => p.type === "Stairs" && String(p.id).startsWith(startFloor));
  if (!stairsStart.length) return setStatus("No stairs found on start floor");

  const nearestStartStair = stairsStart.reduce((best, stair) => {
    const d = distMeters(sPoi.coord, stair.coord);
    return !best || d < best.dist ? { stair, dist: d } : best;
  }, null).stair;

  // 2. Matching stair on target floor (same name)
  const stairEnd = poiItems.find(p =>
    p.type === "Stairs" &&
    p.name === nearestStartStair.name &&
    String(p.id).startsWith(endFloor)
  );
  if (!stairEnd) return setStatus("No matching stair on target floor");

  // 3. Path start → stair (start floor)
  const { node: sNode } = graph.nearestNodeToCoord(sPoi.coord);
  const { node: stairStartNode } = graph.nearestNodeToCoord(nearestStartStair.coord);
  const path1 = graph.dijkstra(sNode.id, stairStartNode.id);

  // 4. Precompute path stair → destination (end floor)
  await loadFloor(`LT${endFloor}`);
  const { node: stairEndNode } = graph.nearestNodeToCoord(stairEnd.coord);
  const { node: eNode } = graph.nearestNodeToCoord(ePoi.coord);
  const path2 = graph.dijkstra(stairEndNode.id, eNode.id);

  // 5. Reset back to start floor
  await loadFloor(`LT${startFloor}`);

  // 6. Store everything
  segmentPaths = { floor1: path1.coords, floor2: path2.coords };
  targetFloor = `LT${endFloor}`;
  currentSegment = 1;
  stairStartCoord = nearestStartStair.coord;
  stairEndCoord = stairEnd.coord;

  // Start with segment 1
  drawFullRoute(path1.coords, nearestStartStair, rooms);
});




  document.getElementById("clearBtn").addEventListener("click", () => {
    drawRoute({ coords: [] });
    map.getSource("nav-markers")?.setData(emptyFC());
    map.getSource("highlight-room")?.setData(emptyFC());
    setStatus("");
  });

function setStatus(msg) {
  document.getElementById("statusNote").textContent = msg || "";
}

function drawFullRoute(coords, ePoi, rooms) {
  setStatus(`Path length: ${fmt(coords.reduce((a, c, i) => i ? a + distMeters(coords[i-1], c) : 0, 0))}`);

  navPath = coords;
  navEndCoord = coords[coords.length - 1];
  const out = buildCumDistances(navPath);
  navCumDist = out.cum;
  navTotalDist = out.total;
  navDistPos = 0;

  updateNavMarkers(navPath[0], navEndCoord, navPath);
  drawRoute({ coords });

  // highlight if destination is Room
  if (ePoi.type === "Room") {
    const room = rooms.features.find(r => r.properties?.id === ePoi.id);
    if (room) {
      map.getSource("highlight-room")?.setData({
        type: "FeatureCollection",
        features: [room]
      });
    }
  } else {
    map.getSource("highlight-room")?.setData(emptyFC());
  }
}


  function drawRoute(res) {
    map.getSource("route")?.setData({
      type: "FeatureCollection",
      features: [{
        type: "Feature",
        geometry: { type: "LineString", coordinates: res.coords || [] },
        properties: {}
      }]
    });
  }

  function updateNavMarkers(start, end, path) {
    let bearing = 0;
    if (path.length >= 2) {
      bearing = turf.bearing(
        turf.point(path[0]),
        turf.point(path[1])
      );
    }
    map.getSource("nav-markers")?.setData({
      type: "FeatureCollection",
      features: [
        {
          type: "Feature",
          properties: { role: "start", bearing },
          geometry: { type: "Point", coordinates: start }
        },
        {
          type: "Feature",
          properties: { role: "end" },
          geometry: { type: "Point", coordinates: end }
        }
      ]
    });
  }

  // ----------------------------------------------------
  // Sources & Layers
  // ----------------------------------------------------
map.on("load", async () => {
    map.addSource("walkable", { type: "geojson", data: emptyFC() });
    map.addSource("walls-3d", { type: "geojson", data: emptyFC() });
    map.addSource("doors-3d", { type: "geojson", data: emptyFC() });
    map.addSource("rooms", { type: "geojson", data: emptyFC() });
    map.addSource("pois", { type: "geojson", data: emptyFC() });
    map.addSource("route", { type: "geojson", data: emptyFC() });
    map.addSource("nav-markers", { type: "geojson", data: emptyFC() });
    map.addSource("highlight-room", { type: "geojson", data: emptyFC() });

    map.addLayer({ id: "walkable-fill", type: "fill", source: "walkable",
      paint: { "fill-color": "#29a329", "fill-opacity": 0.15 } });
map.addLayer({
  id: "walls-3d-extrusion",
  type: "fill-extrusion",
  source: "walls-3d",
  paint: {
    "fill-extrusion-color": "#b0b0b0",
    "fill-extrusion-height": ["get", "height"],  // height in meters
    "fill-extrusion-opacity": 0.95
  }
});

map.addLayer({
  id: "doors-3d-extrusion",
  type: "fill-extrusion",
  source: "doors-3d",
  paint: {
    "fill-extrusion-color": "#5c9ded",
    "fill-extrusion-height": ["get", "height"],  // 0 → flat
    "fill-extrusion-opacity": 0.9
  }
});
    map.addLayer({ id: "pois-symbol", type: "symbol", source: "pois",
      layout: { "icon-image": ["get", "icon"], "icon-size": 1, "icon-anchor": "bottom",
                "text-field": ["get", "name"], "text-offset": [0, 1], "text-size": 12, "text-anchor": "top",
                "icon-allow-overlap": true, "text-allow-overlap": true },
      paint: { "text-color": "#fff", "text-halo-color": "#000", "text-halo-width": 1 } });
    map.addLayer({ id: "route-line", type: "line", source: "route",
      paint: { "line-color": "#00d1b2", "line-width": 6 } });
    map.addLayer({ id: "nav-start", type: "symbol", source: "nav-markers",
      filter: ["==", ["get", "role"], "start"],
      layout: { "icon-image": "start-icon", "icon-size": 0.25, "icon-anchor": "bottom",
                "icon-rotate": ["get", "bearing"], "icon-rotation-alignment": "map",
                "icon-allow-overlap": true } });
    map.addLayer({ id: "nav-end", type: "circle", source: "nav-markers",
      filter: ["==", ["get", "role"], "end"],
      paint: { "circle-radius": 8, "circle-color": "#ff6b6b",
               "circle-stroke-color": "#7a1f1f", "circle-stroke-width": 2 } });
    map.addLayer({ id: "highlight-room-fill", type: "fill", source: "highlight-room",
      paint: { "fill-color": "#ffff00", "fill-opacity": 0.35 } });
    map.addLayer({ id: "highlight-room-outline", type: "line", source: "highlight-room",
      paint: { "line-color": "#ffcc00", "line-width": 3 } });

    // Load default floor
    await loadFloor("LT2");
  });

  // Floor switcher
  document.getElementById("floorSelect").addEventListener("change", (e) => {
    loadFloor(e.target.value);
    
  });

  // Load floor data
  async function loadFloor(floorKey) {
    const f = FLOORS[floorKey]; currentFloor = floorKey;
    const [walls, walkable, doors, rooms, pois, navlines] = await Promise.all([
      fetch(f.walls).then(r => r.json()),
      fetch(f.walkable).then(r => r.json()),
      fetch(f.doors).then(r => r.json()),
      fetch(f.rooms).then(r => r.json()),
      fetch(f.pois).then(r => r.json()),
      f.navlines ? fetch(f.navlines).then(r => r.json()) : Promise.resolve(emptyFC())
    ]);

    const walls3d = toExtrudable(walls, WALL_THICKNESS_M);
      walls3d.features.forEach(f => {
    f.properties = { ...(f.properties || {}), height: 1 };
  });
    const doors3d = toExtrudable(doors, DOOR_THICKNESS_M);
      doors3d.features.forEach(f => {
    f.properties = { ...(f.properties || {}), height: 0 };
  });

    // Filter POIs for current floor
    const filteredPois = filterPoisByFloor(pois, floorKey);

    map.getSource("walls-3d").setData(walls3d);
    map.getSource("doors-3d").setData(doors3d);
    map.getSource("walkable").setData(walkable);
    map.getSource("rooms").setData(rooms);
    map.getSource("pois").setData(filteredPois);

    // Reset navigation state
    navPath = [];
    navEndCoord = null;
    navCumDist = [];
    navTotalDist = 0;
    navDistPos = 0;
    map.getSource("route")?.setData(emptyFC());
    map.getSource("nav-markers")?.setData(emptyFC());
    map.getSource("highlight-room")?.setData(emptyFC());

    // Rebuild routing graph
    graph.nodes.clear();
    for (const feat of navlines.features) {
      if (!feat.geometry) continue;
      const g = feat.geometry;
      if (g.type === "LineString") {
        for (let i = 1; i < g.coordinates.length; i++) {
          graph.addEdge(g.coordinates[i - 1], g.coordinates[i]);
        }
      } else if (g.type === "MultiLineString") {
        for (const line of g.coordinates) {
          for (let i = 1; i < line.length; i++) {
            graph.addEdge(line[i - 1], line[i]);
          }
        }
      }
    }

    fitTo(walkable);
    console.log(`✅ Switched to floor ${floorKey}`);
  }

  // ----------------------------------------------------
  // Animation & Camera
  // ----------------------------------------------------
function animateMove(ts) {
  if (!isMoving || !navPath.length || !navCumDist.length) {
    lastTs = 0;
    return;
  }

  if (!lastTs) lastTs = ts;
  const dt = (ts - lastTs) / 1000;
  lastTs = ts;

  const stepPx = Math.min(MAX_STEP_PX, SPEED_PX_PER_SEC * dt);
  const here = coordAtDistance(navPath, navCumDist, navDistPos).coord || navPath[0];

  const mpp =
    156543.03392 *
    Math.cos(here[1] * Math.PI / 180) /
    Math.pow(2, map.getZoom());

  navDistPos = Math.max(
    0,
    Math.min(navTotalDist, navDistPos + moveDir * stepPx * mpp)
  );

  const pos = coordAtDistance(navPath, navCumDist, navDistPos).coord;
  const ahead = coordAtDistance(navPath, navCumDist, navDistPos + 1).coord || pos;
  const bearing = turf.bearing(turf.point(pos), turf.point(ahead));

  // Update markers
  const feats = [
    { type: "Feature", properties: { role: "start", bearing }, geometry: { type: "Point", coordinates: pos } }
  ];
  if (navEndCoord) {
    feats.push({ type: "Feature", properties: { role: "end" }, geometry: { type: "Point", coordinates: navEndCoord } });
  }
  map.getSource("nav-markers")?.setData({ type: "FeatureCollection", features: feats });

  updateNavCamera(pos, ahead, bearing);

  // 🔄 Switch floors when reaching stair on start floor
  if (currentSegment === 1 && stairStartCoord && distMeters(pos, stairStartCoord) < 0.5) {
    console.log("Reached stairs → switching floor");

    loadFloor(targetFloor).then(() => {
      currentSegment = 2;
      navPath = segmentPaths.floor2;
      navEndCoord = navPath[navPath.length - 1];

      const out = buildCumDistances(navPath);
      navCumDist = out.cum;
      navTotalDist = out.total;
      navDistPos = 0;
    });
  }

  if (moveDir === 1 && Math.abs(navTotalDist - navDistPos) < 0.01) {
    isMoving = false;
  } else {
    requestAnimationFrame(animateMove);
  }
}



  document.addEventListener("keydown", e => {
    if (!navPath.length) return;
    if (e.key === "w" || e.key === "ArrowUp") {
      e.preventDefault();
      keyFwd = true;
    } else if (e.key === "s" || e.key === "ArrowDown") {
      e.preventDefault();
      keyBack = true;
    } else return;

    moveDir = keyFwd ? 1 : (keyBack ? -1 : 0);
    if (moveDir !== 0 && !isMoving) {
      isMoving = true;
      lastTs = 0;
      requestAnimationFrame(animateMove);
    }
  });

  document.addEventListener("keyup", e => {
    if (e.key === "w" || e.key === "ArrowUp") keyFwd = false;
    else if (e.key === "s" || e.key === "ArrowDown") keyBack = false;
    else return;

    moveDir = keyFwd ? 1 : (keyBack ? -1 : 0);
    if (moveDir === 0) isMoving = false;
  });

  function updateNavCamera(pos, ahead, bearing) {
    if (!followCamera) return;

    const bounds = new maplibregl.LngLatBounds(
      new maplibregl.LngLat(...pos),
      new maplibregl.LngLat(...ahead)
    );

    const camNoPad = map.cameraForBounds(bounds, { maxZoom: CAM.maxZoom });
    if (!camNoPad) return;

    const targetZoom = Math.max(
      CAM.minZoom,
      Math.min(CAM.maxZoom, camNoPad.zoom)
    );

    if (camZoomSmoothed == null) camZoomSmoothed = targetZoom;
    camZoomSmoothed = 0.85 * camZoomSmoothed + 0.15 * targetZoom;

    map.easeTo({
      center: pos,
      zoom: camZoomSmoothed,
      bearing,
      pitch: map.getPitch(),
      duration: CAM.easeMs
    });
  }

  // ----------------------------------------------------
  // Fit function
  // ----------------------------------------------------
  function computeBbox(fc) {
    let minX = Infinity,
      minY = Infinity,
      maxX = -Infinity,
      maxY = -Infinity;

    for (const f of fc.features) {
      const geom = f.geometry;
      const eachCoord = c => {
        minX = Math.min(minX, c[0]);
        minY = Math.min(minY, c[1]);
        maxX = Math.max(maxX, c[0]);
        maxY = Math.max(maxY, c[1]);
      };
      if (geom.type === "Point") eachCoord(geom.coordinates);
      else if (geom.type === "LineString") geom.coordinates.forEach(eachCoord);
      else if (geom.type === "Polygon") geom.coordinates.flat().forEach(eachCoord);
      else if (geom.type === "MultiLineString") geom.coordinates.flat().forEach(eachCoord);
      else if (geom.type === "MultiPolygon") geom.coordinates.flat(2).forEach(eachCoord);
      else if (geom.type === "MultiPoint") geom.coordinates.forEach(eachCoord);
    }
    return [[minX, minY], [maxX, maxY]];
  }

  function fitTo(fc) {
    if (!fc || !fc.features?.length) return;
    const bbox = computeBbox(fc);
    map.fitBounds(bbox, { padding: 60, duration: 0 });
  }
})();
