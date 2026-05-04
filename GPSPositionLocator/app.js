let watchId = null;
let currentCoords = null;
let lastPosition = null; // Used for movement filtering
let currentHeading = 0;   // In degrees
const MOVE_THRESHOLD_METERS = 2; // Noise filter: ignore moves < 2m
const toggleBtn = document.getElementById('toggle-btn');
const saveBtn = document.getElementById('save-btn');
const latValue = document.getElementById('lat-value');
const lonValue = document.getElementById('lon-value');
const accuracyValue = document.getElementById('accuracy-value');
const statusText = document.getElementById('status-text');
const compassArrow = document.getElementById('compass-arrow');
const directionLabel = document.getElementById('direction-text');

function startTracking() {
    if (!("geolocation" in navigator)) {
        updateStatus("Geolocation not supported", "error");
        return;
    }

    updateStatus("Requesting permission...", "waiting");

    const options = {
        enableHighAccuracy: true,
        timeout: 10000,
        maximumAge: 0
    };

    watchId = navigator.geolocation.watchPosition(
        (position) => {
            const { latitude, longitude, accuracy } = position.coords;
            currentCoords = { lat: latitude, lon: longitude };
            
            // Movement Filtering & Heading Calculation
            if (lastPosition) {
                // Debug Mode: Always update heading regardless of distance
                currentHeading = calculateBearing(lastPosition.lat, lastPosition.lon, latitude, longitude);
                lastPosition = { lat: latitude, lon: longitude }; 
            } else {
                lastPosition = { lat: latitude, lon: longitude };
            }

            // Update UI
            latValue.textContent = latitude.toFixed(6);
            lonValue.textContent = longitude.toFixed(6);
            accuracyValue.textContent = `${accuracy.toFixed(1)} m`;
            
            // Visual Compass Update
            const cardinal = getCardinal(currentHeading);
            directionLabel.textContent = cardinal;
            compassArrow.style.transform = `rotate(${currentHeading}deg)`;
            document.getElementById('heading-value').textContent = `${Math.round(currentHeading)}°`;
            
            updateStatus("Live Tracking Active", "active");
            saveBtn.style.display = "block";
            
            // Animation effect on value update
            [latValue, lonValue].forEach(el => {
                el.classList.add('pulse');
                setTimeout(() => el.classList.remove('pulse'), 500);
            });
        },
        (error) => {
            console.error(error);
            let msg = "Error occurred";
            switch(error.code) {
                case error.PERMISSION_DENIED:
                    msg = "Permission denied";
                    break;
                case error.POSITION_UNAVAILABLE:
                    msg = "Position unavailable";
                    break;
                case error.TIMEOUT:
                    msg = "Request timed out";
                    break;
            }
            updateStatus(msg, "error");
            stopTracking();
        },
        options
    );

    toggleBtn.textContent = "Stop Tracking";
    toggleBtn.classList.add('stop');
}

function stopTracking() {
    if (watchId !== null) {
        navigator.geolocation.clearWatch(watchId);
        watchId = null;
    }
    toggleBtn.textContent = "Start Tracking";
    toggleBtn.classList.remove('stop');
    saveBtn.style.display = "none";
    updateStatus("Tracking stopped", "waiting");
}

async function saveToGeoJSON() {
    if (!currentCoords) return;

    saveBtn.disabled = true;
    saveBtn.textContent = "Saving...";

    try {
        const response = await fetch('/save-node', {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({ ...currentCoords, heading: Math.round(currentHeading) })
        });

        const result = await response.json();
        if (result.success) {
            updateStatus(`Node saved! (Total: ${result.count})`, "active");
            setTimeout(() => updateStatus("Live Tracking Active", "active"), 2000);
        } else {
            throw new Error(result.error);
        }
    } catch (err) {
        console.error(err);
        updateStatus("Save failed: " + err.message, "error");
    } finally {
        saveBtn.disabled = false;
        saveBtn.textContent = "Save Position";
    }
}

// --- MATH UTILS ---

function calculateDistance(lat1, lon1, lat2, lon2) {
    const R = 6371e3; // Earth radius in meters
    const φ1 = lat1 * Math.PI / 180;
    const φ2 = lat2 * Math.PI / 180;
    const Δφ = (lat2 - lat1) * Math.PI / 180;
    const Δλ = (lon2 - lon1) * Math.PI / 180;

    const a = Math.sin(Δφ/2) * Math.sin(Δφ/2) +
              Math.cos(φ1) * Math.cos(φ2) *
              Math.sin(Δλ/2) * Math.sin(Δλ/2);
    const c = 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1-a));
    return R * c;
}

function calculateBearing(lat1, lon1, lat2, lon2) {
    const φ1 = lat1 * Math.PI / 180;
    const φ2 = lat2 * Math.PI / 180;
    const Δλ = (lon2 - lon1) * Math.PI / 180;

    const y = Math.sin(Δλ) * Math.cos(φ2);
    const x = Math.cos(φ1) * Math.sin(φ2) -
              Math.sin(φ1) * Math.cos(φ2) * Math.cos(Δλ);
    const θ = Math.atan2(y, x);
    return (θ * 180 / Math.PI + 360) % 360; // 0-360 degrees
}

function getCardinal(angle) {
    const directions = ["N", "NE", "E", "SE", "S", "SW", "W", "NW"];
    const index = Math.round(angle / 45) % 8;
    return directions[index];
}

function updateStatus(text, type) {
    statusText.textContent = text;
    statusText.className = `status-value status-${type}`;
}

toggleBtn.addEventListener('click', () => {
    if (watchId === null) {
        startTracking();
    } else {
        stopTracking();
    }
});

saveBtn.addEventListener('click', saveToGeoJSON);
