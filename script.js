const canvas = document.getElementById("dotMap");
const ctx = canvas.getContext("2d");
const legend = document.getElementById("legend");
const profile = document.getElementById("profile");
const selectedProfile = document.getElementById("selectedProfile");
const citySearch = document.getElementById("citySearch");
const searchResults = document.getElementById("searchResults");
const pushModeButton = document.getElementById("pushMode");
const resetButton = document.getElementById("resetDots");
const viewButtons = [...document.querySelectorAll(".view-button")];

const DOT_COUNT = 25000;
const DOT_RADIUS = 0.72;
const DPR_LIMIT = 2;
const STATE_ABBR = {
  "01": "AL",
  "04": "AZ",
  "05": "AR",
  "06": "CA",
  "08": "CO",
  "09": "CT",
  "10": "DE",
  "12": "FL",
  "13": "GA",
  "16": "ID",
  "17": "IL",
  "18": "IN",
  "19": "IA",
  "20": "KS",
  "21": "KY",
  "22": "LA",
  "23": "ME",
  "24": "MD",
  "25": "MA",
  "26": "MI",
  "27": "MN",
  "28": "MS",
  "29": "MO",
  "30": "MT",
  "31": "NE",
  "32": "NV",
  "33": "NH",
  "34": "NJ",
  "35": "NM",
  "36": "NY",
  "37": "NC",
  "38": "ND",
  "39": "OH",
  "40": "OK",
  "41": "OR",
  "42": "PA",
  "44": "RI",
  "45": "SC",
  "46": "SD",
  "47": "TN",
  "48": "TX",
  "49": "UT",
  "50": "VT",
  "51": "VA",
  "53": "WA",
  "54": "WV",
  "55": "WI",
  "56": "WY",
};
const LOWER_48 = new Set([
  "01",
  "04",
  "05",
  "06",
  "08",
  "09",
  "10",
  "12",
  "13",
  "16",
  "17",
  "18",
  "19",
  "20",
  "21",
  "22",
  "23",
  "24",
  "25",
  "26",
  "27",
  "28",
  "29",
  "30",
  "31",
  "32",
  "33",
  "34",
  "35",
  "36",
  "37",
  "38",
  "39",
  "40",
  "41",
  "42",
  "44",
  "45",
  "46",
  "47",
  "48",
  "49",
  "50",
  "51",
  "53",
  "54",
  "55",
  "56",
]);

const views = {
  flag: {
    label:
      "Flag view: 25,000 dots sampled inside real contiguous U.S. state boundaries, colored as a flag pattern across the projected map.",
  },
  population: {
    label:
      "Population density: dot size is based on each dot's nearest Census place population divided by that place's Census gazetteer land area.",
  },
  wealth: {
    label:
      "Wealth: dot size is based on each dot's nearest Census place ACS 2024 5-year median household income.",
  },
  diversity: {
    label:
      "Diversity: dot size is based on each dot's nearest Census place ACS 2024 5-year race/ethnicity composition using a Simpson diversity index.",
  },
  landscape: {
    label:
      "Landscape: dot size is based on Census state land area, emphasizing the physical scale of western and plains states.",
  },
};

let geoFeatures = [];
let stateMetrics = {};
let placesByState = {};
let searchablePlaces = [];
let placeDensityRange = { min: 0, max: 1 };
let placeIncomeRange = { min: 0, max: 1 };
let placeDiversityRange = { min: 0, max: 1 };
let projectedRings = [];
let dots = [];
let activeView = "flag";
let pushMode = false;
let pointer = { x: -9999, y: -9999, active: false };
let hoverDot = null;
let selectedDot = null;
let selectedMarker = null;
let pinnedPlace = null;
let pinnedProfile = false;
let bounds = { minX: 0, minY: 0, maxX: 1, maxY: 1 };
let mapBox = { x: 0, y: 0, w: 1, h: 1 };

function seededRandom(seed) {
  let value = seed;
  return () => {
    value = (value * 1664525 + 1013904223) >>> 0;
    return value / 4294967296;
  };
}

function albersLower48(lon, lat) {
  const phi1 = (29.5 * Math.PI) / 180;
  const phi2 = (45.5 * Math.PI) / 180;
  const phi0 = (37.5 * Math.PI) / 180;
  const lambda0 = (-96 * Math.PI) / 180;
  const phi = (lat * Math.PI) / 180;
  const lambda = (lon * Math.PI) / 180;
  const n = 0.5 * (Math.sin(phi1) + Math.sin(phi2));
  const c = Math.cos(phi1) ** 2 + 2 * n * Math.sin(phi1);
  const rho = Math.sqrt(c - 2 * n * Math.sin(phi)) / n;
  const rho0 = Math.sqrt(c - 2 * n * Math.sin(phi0)) / n;
  const theta = n * (lambda - lambda0);
  return [rho * Math.sin(theta), rho0 - rho * Math.cos(theta)];
}

function pointInRing(x, y, ring) {
  let inside = false;
  for (let i = 0, j = ring.length - 1; i < ring.length; j = i++) {
    const xi = ring[i][0];
    const yi = ring[i][1];
    const xj = ring[j][0];
    const yj = ring[j][1];
    if (yi > y !== yj > y && x < ((xj - xi) * (y - yi)) / (yj - yi) + xi) inside = !inside;
  }
  return inside;
}

function pointInPolygon(x, y, polygon) {
  if (!pointInRing(x, y, polygon[0])) return false;
  for (let i = 1; i < polygon.length; i += 1) {
    if (pointInRing(x, y, polygon[i])) return false;
  }
  return true;
}

function featureContains(feature, x, y) {
  return feature.polygons.some((polygon) => pointInPolygon(x, y, polygon));
}

function projectGeometry() {
  projectedRings = geoFeatures.map((feature) => {
    const coordinates =
      feature.geometry.type === "Polygon" ? [feature.geometry.coordinates] : feature.geometry.coordinates;
    return {
      state: feature.properties.STATE,
      name: feature.properties.NAME,
      polygons: coordinates.map((polygon) =>
        polygon.map((ring) => ring.map(([lon, lat]) => albersLower48(lon, lat))),
      ),
    };
  });

  const allPoints = projectedRings.flatMap((feature) => feature.polygons.flat(2));
  bounds = {
    minX: Math.min(...allPoints.map((p) => p[0])),
    maxX: Math.max(...allPoints.map((p) => p[0])),
    minY: Math.min(...allPoints.map((p) => p[1])),
    maxY: Math.max(...allPoints.map((p) => p[1])),
  };
}

function preparePlaces(places) {
  placesByState = {};
  searchablePlaces = [];
  const densityValues = [];
  const incomeValues = [];
  const diversityValues = [];
  for (const place of places) {
    const [px, py] = albersLower48(place.lon, place.lat);
    const density =
      Number.isFinite(place.population) && Number.isFinite(place.landSqMi) && place.landSqMi > 0
        ? place.population / place.landSqMi
        : null;
    const projected = { ...place, px, py, density };
    projected.displayName = formatPlaceName(projected.name);
    if (Number.isFinite(density)) densityValues.push(density);
    if (Number.isFinite(place.income)) incomeValues.push(place.income);
    if (Number.isFinite(place.diversity)) diversityValues.push(place.diversity);
    if (!placesByState[place.state]) placesByState[place.state] = [];
    placesByState[place.state].push(projected);
    searchablePlaces.push({
      ...projected,
      searchText: `${projected.displayName} ${STATE_ABBR[projected.state] || ""}`.toLowerCase(),
    });
  }
  densityValues.sort((a, b) => a - b);
  incomeValues.sort((a, b) => a - b);
  diversityValues.sort((a, b) => a - b);
  placeDensityRange = {
    min: densityValues[Math.floor(densityValues.length * 0.02)] || 0,
    max: densityValues[Math.floor(densityValues.length * 0.98)] || 1,
  };
  placeIncomeRange = {
    min: incomeValues[Math.floor(incomeValues.length * 0.02)] || 0,
    max: incomeValues[Math.floor(incomeValues.length * 0.98)] || 1,
  };
  placeDiversityRange = {
    min: diversityValues[Math.floor(diversityValues.length * 0.02)] || 0,
    max: diversityValues[Math.floor(diversityValues.length * 0.98)] || 1,
  };
}

function formatPlaceName(name) {
  if (!name) return "";
  const lowerWords = new Set(["of", "the", "and"]);
  return name
    .split(/\s+/)
    .map((word, index) => {
      if (index > 0 && lowerWords.has(word.toLowerCase())) return word.toLowerCase();
      if (/^[A-Z]{2,}$/.test(word)) return word;
      if (word.includes("-")) return word.split("-").map((part) => formatPlaceName(part)).join("-");
      return word.charAt(0).toUpperCase() + word.slice(1);
    })
    .join(" ");
}

function nearestDotToPlace(place) {
  let best = null;
  let bestDist = Infinity;
  for (const dot of dots) {
    if (dot.state !== place.state) continue;
    const dx = dot.px - place.px;
    const dy = dot.py - place.py;
    const dist = dx * dx + dy * dy;
    if (dist < bestDist) {
      best = dot;
      bestDist = dist;
    }
  }
  return best;
}

function nearestPlace(dot) {
  const places = placesByState[dot.state] || [];
  let best = null;
  let bestDist = Infinity;
  for (const place of places) {
    const dx = dot.px - place.px;
    const dy = dot.py - place.py;
    const dist = dx * dx + dy * dy;
    if (dist < bestDist) {
      best = place;
      bestDist = dist;
    }
  }
  return best;
}

function generateDots() {
  const rand = seededRandom(1776);
  const candidates = [];
  let guard = 0;

  while (candidates.length < DOT_COUNT && guard < DOT_COUNT * 250) {
    guard += 1;
    const x = bounds.minX + rand() * (bounds.maxX - bounds.minX);
    const y = bounds.minY + rand() * (bounds.maxY - bounds.minY);
    const feature = projectedRings.find((candidate) => featureContains(candidate, x, y));
    if (feature) {
      candidates.push({
        px: x,
        py: y,
        state: feature.state,
        stateName: feature.name,
        jitter: rand(),
      });
    }
  }

  dots = candidates
    .sort((a, b) => a.jitter - b.jitter)
    .slice(0, DOT_COUNT)
    .map((dot, index) => ({
      ...dot,
      index,
      nx: (dot.px - bounds.minX) / (bounds.maxX - bounds.minX),
      ny: 1 - (dot.py - bounds.minY) / (bounds.maxY - bounds.minY),
      place: nearestPlace(dot),
      x: 0,
      y: 0,
      tx: 0,
      ty: 0,
      vx: 0,
      vy: 0,
      size: DOT_RADIUS,
      targetSize: DOT_RADIUS,
      color: "#fff",
    }));
}

function resize() {
  const rect = canvas.parentElement.getBoundingClientRect();
  const dpr = Math.min(window.devicePixelRatio || 1, DPR_LIMIT);
  canvas.width = Math.floor(rect.width * dpr);
  canvas.height = Math.floor(rect.height * dpr);
  canvas.style.width = `${rect.width}px`;
  canvas.style.height = `${rect.height}px`;
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);

  const marginX = Math.max(24, rect.width * 0.045);
  const marginY = Math.max(42, rect.height * 0.1);
  const naturalRatio = (bounds.maxX - bounds.minX) / (bounds.maxY - bounds.minY);
  let mapW = rect.width - marginX * 2;
  let mapH = mapW / naturalRatio;
  if (mapH > rect.height - marginY * 2) {
    mapH = rect.height - marginY * 2;
    mapW = mapH * naturalRatio;
  }
  mapBox = {
    x: (rect.width - mapW) / 2,
    y: Math.max(22, (rect.height - mapH) / 2 - 8),
    w: mapW,
    h: mapH,
  };

  for (const dot of dots) {
    dot.tx = mapBox.x + dot.nx * mapBox.w;
    dot.ty = mapBox.y + dot.ny * mapBox.h;
    if (!dot.x && !dot.y) {
      dot.x = dot.tx;
      dot.y = dot.ty;
    }
  }

  if (selectedMarker) {
    positionSelectedMarker();
    if (pinnedPlace) renderPinnedPlaceProfile(pinnedPlace);
  }
}

function positionSelectedMarker() {
  selectedMarker.x = mapBox.x + selectedMarker.nx * mapBox.w;
  selectedMarker.y = mapBox.y + selectedMarker.ny * mapBox.h;
}

function colorForFlag(dot) {
  if (dot.nx < 0.38 && dot.ny < 0.48) return "#244a86";
  const stripe = Math.floor(dot.ny * 13);
  return stripe % 2 === 0 ? "#bd3341" : "#f8f7f1";
}

function metricForDot(dot, view) {
  const metrics = stateMetrics[dot.state];
  if (!metrics) return 0;
  if (view === "population") {
    if (Number.isFinite(dot.place?.density)) {
      return Math.max(
        0,
        Math.min(1, (dot.place.density - placeDensityRange.min) / (placeDensityRange.max - placeDensityRange.min)),
      );
    }
    return metrics.densityNorm;
  }
  if (view === "wealth") {
    if (Number.isFinite(dot.place?.income)) {
      return Math.max(
        0,
        Math.min(1, (dot.place.income - placeIncomeRange.min) / (placeIncomeRange.max - placeIncomeRange.min)),
      );
    }
    return metrics.incomeNorm;
  }
  if (view === "diversity") {
    if (Number.isFinite(dot.place?.diversity)) {
      return Math.max(
        0,
        Math.min(
          1,
          (dot.place.diversity - placeDiversityRange.min) /
            (placeDiversityRange.max - placeDiversityRange.min),
        ),
      );
    }
    return metrics.diversityNorm;
  }
  if (view === "landscape") return metrics.landAreaNorm;
  return 0;
}

function colorForView(view, score) {
  if (view === "population") return `rgb(${160 + score * 75}, ${46 + score * 42}, ${54 + score * 24})`;
  if (view === "wealth") return `rgb(${186 + score * 48}, ${127 + score * 62}, ${42 + score * 38})`;
  if (view === "diversity") return `rgb(${52 + score * 54}, ${103 + score * 82}, ${116 + score * 72})`;
  return `rgb(${67 + score * 58}, ${103 + score * 65}, ${74 + score * 34})`;
}

function setView(view) {
  activeView = view;
  legend.textContent = views[view].label;
  viewButtons.forEach((button) => button.classList.toggle("active", button.dataset.view === view));

  for (const dot of dots) {
    const score = metricForDot(dot, view);
    dot.targetSize = view === "flag" ? DOT_RADIUS : DOT_RADIUS * (0.85 + score * 3.6);
    dot.color = view === "flag" ? colorForFlag(dot) : colorForView(view, score);
  }
}

function resetDots() {
  for (const dot of dots) {
    dot.vx = 0;
    dot.vy = 0;
  }
}

function clearPins() {
  pinnedProfile = false;
  hoverDot = null;
  selectedDot = null;
  selectedMarker = null;
  pinnedPlace = null;
  profile.classList.remove("visible", "pinned");
  selectedProfile.classList.remove("visible");
}

function resetMap() {
  resetDots();
  clearPins();
}

function drawStateOutlines() {
  ctx.save();
  ctx.strokeStyle = "rgba(23, 32, 42, 0.12)";
  ctx.lineWidth = 0.8;
  for (const feature of projectedRings) {
    for (const polygon of feature.polygons) {
      for (const ring of polygon) {
        ctx.beginPath();
        for (const [i, point] of ring.entries()) {
          const x = mapBox.x + ((point[0] - bounds.minX) / (bounds.maxX - bounds.minX)) * mapBox.w;
          const y =
            mapBox.y + (1 - (point[1] - bounds.minY) / (bounds.maxY - bounds.minY)) * mapBox.h;
          if (i === 0) ctx.moveTo(x, y);
          else ctx.lineTo(x, y);
        }
        ctx.stroke();
      }
    }
  }
  ctx.restore();
}

function animate() {
  ctx.clearRect(0, 0, canvas.clientWidth, canvas.clientHeight);
  drawStateOutlines();

  for (const dot of dots) {
    if (pushMode && pointer.active) {
      const dx = dot.x - pointer.x;
      const dy = dot.y - pointer.y;
      const distSq = dx * dx + dy * dy;
      const radius = Math.max(74, mapBox.w * 0.07);
      if (distSq < radius * radius) {
        const dist = Math.sqrt(distSq) || 1;
        const force = (1 - dist / radius) * 1.35;
        dot.vx += (dx / dist) * force;
        dot.vy += (dy / dist) * force;
      }
    }

    dot.vx += (dot.tx - dot.x) * 0.025;
    dot.vy += (dot.ty - dot.y) * 0.025;
    dot.vx *= 0.86;
    dot.vy *= 0.86;
    dot.x += dot.vx;
    dot.y += dot.vy;
    dot.size += (dot.targetSize - dot.size) * 0.12;
    const displaySize = dot === selectedDot ? Math.max(dot.size * 3.2, 6.5) : dot.size;

    ctx.beginPath();
    ctx.fillStyle = dot.color;
    ctx.arc(dot.x, dot.y, displaySize, 0, Math.PI * 2);
    ctx.fill();
    if (dot.color === "#f8f7f1") {
      ctx.strokeStyle = "rgba(23, 32, 42, 0.16)";
      ctx.lineWidth = 0.55;
      ctx.stroke();
    }
  }

  if (hoverDot) {
    ctx.save();
    ctx.beginPath();
    ctx.strokeStyle = "rgba(23, 32, 42, 0.72)";
    ctx.lineWidth = 1.6;
    ctx.arc(hoverDot.x, hoverDot.y, Math.max(hoverDot.size + 3.5, 5), 0, Math.PI * 2);
    ctx.stroke();
    ctx.restore();
  }

  if (selectedMarker) {
    ctx.save();
    ctx.beginPath();
    ctx.fillStyle = "#ffffff";
    ctx.arc(selectedMarker.x, selectedMarker.y, 9.5, 0, Math.PI * 2);
    ctx.fill();
    ctx.beginPath();
    ctx.strokeStyle = "#17202a";
    ctx.lineWidth = 2.6;
    ctx.arc(selectedMarker.x, selectedMarker.y, 10, 0, Math.PI * 2);
    ctx.stroke();
    ctx.beginPath();
    ctx.fillStyle = selectedMarker.color;
    ctx.arc(selectedMarker.x, selectedMarker.y, 6.6, 0, Math.PI * 2);
    ctx.fill();
    ctx.beginPath();
    ctx.strokeStyle = "#ffffff";
    ctx.lineWidth = 1.6;
    ctx.arc(selectedMarker.x, selectedMarker.y, 6.6, 0, Math.PI * 2);
    ctx.stroke();
    ctx.restore();
  }

  requestAnimationFrame(animate);
}

function formatNumber(value) {
  return Number.isFinite(value) ? Math.round(value).toLocaleString("en-US") : "Not reported";
}

function formatMoney(value) {
  return Number.isFinite(value)
    ? `$${Math.round(value).toLocaleString("en-US")}`
    : "Not reported";
}

function formatPercent(value) {
  return Number.isFinite(value) ? `${Math.round(value * 100)} / 100` : "Not reported";
}

function pointerInsideMap() {
  const mapPad = 28;
  return (
    pointer.x >= mapBox.x - mapPad &&
    pointer.x <= mapBox.x + mapBox.w + mapPad &&
    pointer.y >= mapBox.y - mapPad &&
    pointer.y <= mapBox.y + mapBox.h + mapPad
  );
}

function nearestDotToPointer() {
  let best = null;
  let bestDist = Infinity;
  for (const dot of dots) {
    const dx = dot.x - pointer.x;
    const dy = dot.y - pointer.y;
    const dist = dx * dx + dy * dy;
    if (dist < bestDist) {
      best = dot;
      bestDist = dist;
    }
  }
  return best;
}

function renderProfile(dot, placeOverride = null) {
  if (!dot) {
    hoverDot = null;
    profile.classList.remove("visible");
    return;
  }

  hoverDot = dot;
  const place = placeOverride || dot.place;
  const state = stateMetrics[dot.state];
  profile.innerHTML = `
    <h2>${place ? place.displayName || formatPlaceName(place.name) : dot.stateName}</h2>
    <dl>
      <dt>State</dt><dd>${dot.stateName}</dd>
      <dt>Place population</dt><dd>${formatNumber(place?.population)}</dd>
      <dt>Place density</dt><dd>${Number.isFinite(place?.density) ? `${Math.round(place.density).toLocaleString("en-US")} / sq mi` : "Not reported"}</dd>
      <dt>Median income</dt><dd>${formatMoney(place?.income)}</dd>
      <dt>Diversity index</dt><dd>${formatPercent(place?.diversity)}</dd>
      <dt>Place land area</dt><dd>${Number.isFinite(place?.landSqMi) ? `${place.landSqMi.toLocaleString("en-US")} sq mi` : "Not reported"}</dd>
      <dt>State density</dt><dd>${Number.isFinite(state?.density) ? `${Math.round(state.density).toLocaleString("en-US")} / sq mi` : "Not reported"}</dd>
    </dl>
    <p>Nearest Census place centroid to this dot within ${dot.stateName}; ACS 2024 5-year estimates where available.</p>
  `;

  const rect = canvas.getBoundingClientRect();
  const profileWidth = 272;
  const profileHeight = 236;
  const x = Math.min(Math.max(pointer.x + 16, 12), rect.width - profileWidth - 12);
  const y = Math.min(Math.max(pointer.y + 16, 12), rect.height - profileHeight - 12);
  profile.style.transform = `translate(${x}px, ${y}px)`;
  profile.classList.add("visible");
}

function renderPinnedPlaceProfile(place) {
  const state = stateMetrics[place.state];
  const stateName = state?.name || STATE_ABBR[place.state] || "";
  selectedProfile.innerHTML = `
    <h2>${place.displayName || formatPlaceName(place.name)}</h2>
    <dl>
      <dt>State</dt><dd>${stateName}</dd>
      <dt>Place population</dt><dd>${formatNumber(place.population)}</dd>
      <dt>Place density</dt><dd>${Number.isFinite(place.density) ? `${Math.round(place.density).toLocaleString("en-US")} / sq mi` : "Not reported"}</dd>
      <dt>Median income</dt><dd>${formatMoney(place.income)}</dd>
      <dt>Diversity index</dt><dd>${formatPercent(place.diversity)}</dd>
      <dt>Place land area</dt><dd>${Number.isFinite(place.landSqMi) ? `${place.landSqMi.toLocaleString("en-US")} sq mi` : "Not reported"}</dd>
      <dt>State density</dt><dd>${Number.isFinite(state?.density) ? `${Math.round(state.density).toLocaleString("en-US")} / sq mi` : "Not reported"}</dd>
    </dl>
    <p>Pinned Census place centroid; ACS 2024 5-year estimates where available.</p>
  `;
  selectedProfile.classList.add("visible");
  profile.classList.remove("visible", "pinned");
}

function clearSearchResults() {
  searchResults.classList.remove("visible");
  searchResults.innerHTML = "";
}

function resultSubtitle(place) {
  const parts = [STATE_ABBR[place.state] || ""];
  if (Number.isFinite(place.population)) parts.push(`pop. ${formatNumber(place.population)}`);
  if (Number.isFinite(place.density)) parts.push(`${Math.round(place.density).toLocaleString("en-US")} / sq mi`);
  return parts.filter(Boolean).join(" · ");
}

function selectPlace(place) {
  const dot = nearestDotToPlace(place);
  if (!dot) return;
  const nx = (place.px - bounds.minX) / (bounds.maxX - bounds.minX);
  const ny = 1 - (place.py - bounds.minY) / (bounds.maxY - bounds.minY);
  selectedDot = null;
  selectedMarker = {
    place,
    state: place.state,
    stateName: dot.stateName,
    nx,
    ny,
    x: 0,
    y: 0,
    color: colorForView(activeView === "flag" ? "population" : activeView, metricForDot(dot, activeView)),
  };
  positionSelectedMarker();
  pointer.x = selectedMarker.x;
  pointer.y = selectedMarker.y;
  pointer.active = true;
  pinnedProfile = true;
  pinnedPlace = place;
  hoverDot = null;
  renderPinnedPlaceProfile(place);
  resetDots();
  dot.vx += 0.01;
  citySearch.value = `${place.displayName || formatPlaceName(place.name)}, ${STATE_ABBR[place.state] || ""}`;
  clearSearchResults();
  citySearch.blur();
}

function updateSearchResults() {
  const query = citySearch.value.trim().toLowerCase();
  if (query.length < 2) {
    clearSearchResults();
    return;
  }

  const normalized = query.replace(",", " ");
  const matches = searchablePlaces
    .filter((place) => place.searchText.includes(normalized))
    .sort((a, b) => {
      const aExact = a.displayName.toLowerCase().startsWith(query) ? 0 : 1;
      const bExact = b.displayName.toLowerCase().startsWith(query) ? 0 : 1;
      if (aExact !== bExact) return aExact - bExact;
      return (b.population || 0) - (a.population || 0);
    })
    .slice(0, 8);

  if (!matches.length) {
    searchResults.innerHTML = `<div class="search-empty">No Census places found</div>`;
    searchResults.classList.add("visible");
    return;
  }

  searchResults.innerHTML = "";
  for (const place of matches) {
    const button = document.createElement("button");
    button.type = "button";
    button.className = "search-result";
    button.setAttribute("role", "option");
    button.innerHTML = `<strong>${place.displayName}</strong><span>${resultSubtitle(place)}</span>`;
    button.addEventListener("mousedown", (event) => event.preventDefault());
    button.addEventListener("click", () => selectPlace(place));
    searchResults.appendChild(button);
  }
  searchResults.classList.add("visible");
}

function updateHoverProfile() {
  if (pinnedProfile) return;
  if (!pointer.active || pushMode) {
    hoverDot = null;
    profile.classList.remove("visible");
    return;
  }

  if (!pointerInsideMap()) {
    hoverDot = null;
    profile.classList.remove("visible");
    return;
  }

  renderProfile(nearestDotToPointer());
}

function setPointer(event, active = true) {
  const rect = canvas.getBoundingClientRect();
  pointer.x = event.clientX - rect.left;
  pointer.y = event.clientY - rect.top;
  pointer.active = active;
  updateHoverProfile();
}

function eventIsOverCanvas(event) {
  const element = document.elementFromPoint(event.clientX, event.clientY);
  return element === canvas;
}

function setPointerFromDocument(event) {
  if (eventIsOverCanvas(event)) setPointer(event, true);
}

function togglePinnedProfile(event) {
  if (pushMode) return;
  const rect = canvas.getBoundingClientRect();
  pointer.x = event.clientX - rect.left;
  pointer.y = event.clientY - rect.top;
  pointer.active = true;
  if (pinnedProfile) {
    pinnedProfile = false;
    selectedDot = null;
    profile.classList.remove("pinned");
    updateHoverProfile();
    return;
  }

  if (!pointerInsideMap()) return;
  selectedDot = null;
  renderProfile(nearestDotToPointer());
  if (hoverDot) {
    pinnedProfile = true;
    profile.classList.add("visible", "pinned");
  }
}

async function init() {
  const [geo, metrics, places] = await Promise.all([
    fetch("us-states.json").then((response) => response.json()),
    fetch("state-metrics.json").then((response) => response.json()),
    fetch("place-profiles.json").then((response) => response.json()),
  ]);
  geoFeatures = geo.features.filter((feature) => LOWER_48.has(feature.properties.STATE));
  stateMetrics = metrics.states;
  projectGeometry();
  preparePlaces(places.places);
  generateDots();
  resize();
  setView("flag");
  animate();
}

window.addEventListener("resize", resize);
canvas.addEventListener("pointermove", (event) => setPointer(event, true));
canvas.addEventListener("pointerenter", (event) => setPointer(event, true));
canvas.addEventListener("mousemove", (event) => setPointer(event, true));
canvas.addEventListener("mouseenter", (event) => setPointer(event, true));
canvas.onmousemove = (event) => setPointer(event, true);
document.addEventListener("mousemove", setPointerFromDocument);
canvas.addEventListener("pointerleave", () => {
  pointer.active = false;
  if (!pinnedProfile) {
    hoverDot = null;
    profile.classList.remove("visible");
  }
});
canvas.addEventListener("mouseleave", () => {
  pointer.active = false;
  if (!pinnedProfile) {
    hoverDot = null;
    profile.classList.remove("visible");
  }
});
canvas.addEventListener("click", (event) => {
  event.stopPropagation();
  togglePinnedProfile(event);
});
document.addEventListener("click", (event) => {
  if (eventIsOverCanvas(event)) togglePinnedProfile(event);
  else if (!searchResults.contains(event.target) && event.target !== citySearch) clearSearchResults();
});

citySearch.addEventListener("input", updateSearchResults);
citySearch.addEventListener("focus", updateSearchResults);
citySearch.addEventListener("keydown", (event) => {
  const first = searchResults.querySelector(".search-result");
  if (event.key === "Enter" && first) {
    event.preventDefault();
    first.click();
  }
  if (event.key === "Escape") clearSearchResults();
});

pushModeButton.addEventListener("click", () => {
  pushMode = !pushMode;
  clearPins();
  pushModeButton.classList.toggle("active", pushMode);
  pushModeButton.setAttribute("aria-pressed", String(pushMode));
  canvas.classList.toggle("pushing", pushMode);
});

resetButton.addEventListener("click", resetMap);
viewButtons.forEach((button) => button.addEventListener("click", () => setView(button.dataset.view)));

init().catch((error) => {
  legend.textContent = "Map data failed to load. Start a local server and reload the page.";
  throw error;
});
