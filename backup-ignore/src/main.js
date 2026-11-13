import * as THREE from 'three';

const TILE_SIZE = 2.5;
const GROUND_TILES = 40;
const GROUND_SIZE = TILE_SIZE * GROUND_TILES;

const MAN_COUNT = 120;
const SPAWN_RADIUS = 45;
const MAN_WIDTH = 1.2;
const MAN_HEIGHT = 1.8;

const EYE_HEIGHT = 1.65;
const MOVE_ACCEL = 26;
const MOVE_DAMPING = 5.5;
const ANG_ACCEL = 18;
const ANG_DAMPING = 9.0;

const CELL_SIZE = 4.2;
const WALL_HEIGHT = 3.2;
const WALL_THICKNESS = 0.45;
const WALL_VIEW_RADIUS = 8;
const MAX_WALL_INSTANCES = (WALL_VIEW_RADIUS * 2 + 2) * (WALL_VIEW_RADIUS * 2 + 2);
const PLAYER_RADIUS = 0.45;
const MAN_RADIUS = 0.4;

const ANXIETY_TYPO_PENALTY = 5;
const CLOSE_RADIUS = 5.5;
const ANXIETY_PROXIMITY_RATE = 3.5;
const FOOTSTEP_RADIUS = 18;

const MAZE_CHUNK_SIZE = 8;
const mazeChunks = new Map();

function createChunkRng(cx, cz) {
  let state = (Math.imul(cx, 374761393) ^ Math.imul(cz, 668265263) ^ 0x9e3779b9) >>> 0;
  return () => {
    state = (state + 0x6d2b79f5) >>> 0;
    let t = Math.imul(state ^ (state >>> 15), 1 | state);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function getMazeChunk(cx, cz) {
  const key = `${cx},${cz}`;
  let data = mazeChunks.get(key);
  if (data) return data;

  const N = MAZE_CHUNK_SIZE;
  data = new Uint8Array(N * N);
  data.fill(3); // bit 1 = North wall, bit 2 = West wall

  const visited = new Uint8Array(N * N);
  const rand = createChunkRng(cx, cz);
  const stack = [[0, 0]];
  visited[0] = 1;

  while (stack.length > 0) {
    const [x, z] = stack[stack.length - 1];
    const neighbors = [];
    if (z > 0 && !visited[(z - 1) * N + x]) neighbors.push([x, z - 1, 0]);
    if (z < N - 1 && !visited[(z + 1) * N + x]) neighbors.push([x, z + 1, 1]);
    if (x > 0 && !visited[z * N + (x - 1)]) neighbors.push([x - 1, z, 2]);
    if (x < N - 1 && !visited[z * N + (x + 1)]) neighbors.push([x + 1, z, 3]);

    if (neighbors.length === 0) {
      stack.pop();
      continue;
    }

    const [nx, nz, dir] = neighbors[Math.floor(rand() * neighbors.length)];
    if (dir === 0) data[z * N + x] &= ~1;
    else if (dir === 1) data[nz * N + nx] &= ~1;
    else if (dir === 2) data[z * N + x] &= ~2;
    else if (dir === 3) data[nz * N + nx] &= ~2;

    visited[nz * N + nx] = 1;
    stack.push([nx, nz]);
  }

  // Open 3 doorways along North and West chunk borders for endless connectivity
  for (let d = 0; d < 3; d++) {
    const bx = Math.floor(rand() * N);
    data[bx] &= ~1;
    const bz = Math.floor(rand() * N);
    data[bz * N] &= ~2;
  }

  // Open a few extra interior loops (~8%) so corridors aren't strictly single-path
  for (let z = 1; z < N; z++) {
    for (let x = 1; x < N; x++) {
      if (rand() < 0.08) data[z * N + x] &= ~1;
      if (rand() < 0.08) data[z * N + x] &= ~2;
    }
  }

  // Give player a small clear starting area around (0, 0)
  if (cx === 0 && cz === 0) {
    data[0] &= ~3;
    data[1] &= ~2;
    data[N] &= ~1;
  }

  mazeChunks.set(key, data);
  return data;
}

function getMazeCellBits(gx, gz) {
  const cx = Math.floor(gx / MAZE_CHUNK_SIZE);
  const cz = Math.floor(gz / MAZE_CHUNK_SIZE);
  const lx = ((gx % MAZE_CHUNK_SIZE) + MAZE_CHUNK_SIZE) % MAZE_CHUNK_SIZE;
  const lz = ((gz % MAZE_CHUNK_SIZE) + MAZE_CHUNK_SIZE) % MAZE_CHUNK_SIZE;
  return getMazeChunk(cx, cz)[lz * MAZE_CHUNK_SIZE + lx];
}

function hasHWall(gx, gz) {
  return (getMazeCellBits(gx, gz) & 1) !== 0;
}

function hasVWall(gx, gz) {
  return (getMazeCellBits(gx, gz) & 2) !== 0;
}

function resolveCircleAABB(entity, radius, minX, maxX, minZ, maxZ, isPlayer) {
  const cx = Math.max(minX, Math.min(entity.x, maxX));
  const cz = Math.max(minZ, Math.min(entity.z, maxZ));
  const dx = entity.x - cx;
  const dz = entity.z - cz;
  const distSq = dx * dx + dz * dz;

  if (distSq >= radius * radius) return false;

  let nx = 0;
  let nz = 0;
  let overlap = 0;

  if (distSq > 1e-8) {
    const dist = Math.sqrt(distSq);
    nx = dx / dist;
    nz = dz / dist;
    overlap = radius - dist;
  } else {
    const left = entity.x - minX;
    const right = maxX - entity.x;
    const top = entity.z - minZ;
    const bottom = maxZ - entity.z;
    const minPen = Math.min(left, right, top, bottom);
    if (minPen === left) {
      nx = -1;
      overlap = left + radius;
    } else if (minPen === right) {
      nx = 1;
      overlap = right + radius;
    } else if (minPen === top) {
      nz = -1;
      overlap = top + radius;
    } else {
      nz = 1;
      overlap = bottom + radius;
    }
  }

  entity.x += nx * overlap;
  entity.z += nz * overlap;

  if (isPlayer) {
    const vn = entity.vx * nx + entity.vz * nz;
    if (vn < 0) {
      entity.vx -= vn * nx;
      entity.vz -= vn * nz;
    }
  } else {
    const dirX = Math.sin(entity.angle);
    const dirZ = Math.cos(entity.angle);
    const dn = dirX * nx + dirZ * nz;
    if (dn < 0) {
      const rx = dirX - 2 * dn * nx;
      const rz = dirZ - 2 * dn * nz;
      entity.angle = Math.atan2(rx, rz);
    }
  }

  return true;
}

function resolveWallCollisions(entity, radius, isPlayer) {
  const gxCenter = Math.floor(entity.x / CELL_SIZE);
  const gzCenter = Math.floor(entity.z / CELL_SIZE);
  const halfT = WALL_THICKNESS * 0.5;

  for (let gx = gxCenter - 1; gx <= gxCenter + 2; gx++) {
    for (let gz = gzCenter - 1; gz <= gzCenter + 2; gz++) {
      if (hasHWall(gx, gz)) {
        const minX = gx * CELL_SIZE - halfT;
        const maxX = (gx + 1) * CELL_SIZE + halfT;
        const minZ = gz * CELL_SIZE - halfT;
        const maxZ = gz * CELL_SIZE + halfT;
        resolveCircleAABB(entity, radius, minX, maxX, minZ, maxZ, isPlayer);
      }
      if (hasVWall(gx, gz)) {
        const minX = gx * CELL_SIZE - halfT;
        const maxX = gx * CELL_SIZE + halfT;
        const minZ = gz * CELL_SIZE - halfT;
        const maxZ = (gz + 1) * CELL_SIZE + halfT;
        resolveCircleAABB(entity, radius, minX, maxX, minZ, maxZ, isPlayer);
      }
    }
  }
}

const PHRASES = [
  'so how about this weather',
  'working hard or hardly working',
  'is it friday yet or what',
  'crazy humidity we are having',
  'nice shoes where are they from',
  'big plans for the weekend',
  'how was your commute today',
  'living the dream over here',
  'cannot complain nobody listens',
  'we really needed this rain',
  'staying out of trouble lately',
  'long time no see stranger',
  'how is the family doing',
  'did you watch the game',
  'sure is a monday today',
  'love that shirt on you',
  'getting enough sleep these days',
  'traffic was a nightmare earlier',
  'any fun vacations coming up',
  'have you tried that new place',
  'coffee has not kicked in yet',
  'it is not the heat its humidity',
  'time flies when you are awake',
  'what did you have for lunch',
  'is that a new haircut',
  'you look exactly the same',
  'busy week ahead of us',
  'i am just taking it easy',
  'another day another dollar',
  'weather app lied to me again',
  'do you come here often',
  'looks like it might snow soon',
  'my knees know when it rains',
  'i forgot why i walked in here',
  'have you seen anything good lately',
  'still reading that same book',
  'i need a vacation from my vacation',
  'how is your dog doing',
  'my back hurts for no reason',
  'i almost cooked dinner tonight',
  'they moved the yogurt aisle again',
  'rent is wild these days',
  'did you get my email earlier',
  'funny running into you here',
  'what a small world after all',
  'i should really drink more water',
  'i went to bed at nine yesterday',
  'these fluorescent lights are loud',
  'is this seat taken by anyone',
  'tell your cat i said hi',
  'i love a good spreadsheet',
  'my plants are barely hanging on',
  'have you tried turning it off',
  'i think i left the stove on',
  'we should catch up sometime soon',
  'let us circle back on that',
  'that is just how the cookie crumbles',
  'cold enough for you out there',
  'i am strictly a decaf person now',
  'parking here is an extreme sport',
  'did you hear about the raccoons',
  'i bought too many bananas again',
  'this carpet feels familiar somehow',
  'my dentist asked about you',
  'i am trying to cut back on soup',
  'do you prefer stairs or elevators',
  'i only came for the free napkins',
  'how do you feel about tuesdays',
  'my neighbor mows at six am',
  'i lost my favorite spoon yesterday',
  'that ceiling tile looks suspicious',
  'have a great rest of your day',
  'we are all just winging it',
  'i brought leftovers again today',
  'do you ever just stare at walls',
  'my umbrella turned inside out',
  'i am allergic to mornings honestly',
  'keep the change you earned it',
  'see you around the water cooler',
  'take care drive safe out there',
];

function splitPhraseCentered(ctx, phrase, maxW) {
  if (ctx.measureText(phrase).width <= maxW) {
    return { line1: phrase, line2: null, splitIdx: phrase.length };
  }
  const mid = phrase.length * 0.5;
  let bestSplit = -1;
  let bestDist = Infinity;
  for (let idx = 0; idx < phrase.length; idx++) {
    if (phrase[idx] === ' ') {
      const dist = Math.abs(idx - mid);
      if (dist < bestDist) {
        bestDist = dist;
        bestSplit = idx;
      }
    }
  }
  if (bestSplit === -1) {
    return { line1: phrase, line2: null, splitIdx: phrase.length };
  }
  return {
    line1: phrase.slice(0, bestSplit),
    line2: phrase.slice(bestSplit + 1),
    splitIdx: bestSplit,
  };
}

function createPhraseAtlasTexture(phrases) {
  const cols = 8;
  const rows = Math.ceil(phrases.length / cols);
  const cellW = 384;
  const cellH = 96;

  const canvas = document.createElement('canvas');
  canvas.width = cols * cellW;
  canvas.height = rows * cellH;
  const ctx = canvas.getContext('2d');

  ctx.clearRect(0, 0, canvas.width, canvas.height);
  ctx.textAlign = 'center';
  ctx.textBaseline = 'middle';
  ctx.lineJoin = 'round';

  const charEndUV = [];

  for (let i = 0; i < phrases.length; i++) {
    const phrase = phrases[i];
    const col = i % cols;
    const row = Math.floor(i / cols);
    const cellX = col * cellW;
    const cellY = row * cellH;
    const cx = cellX + cellW * 0.5;

    let fontSize = 28;
    ctx.font = `${fontSize}px "Abaddon Bold", sans-serif`;
    const { line1, line2, splitIdx } = splitPhraseCentered(ctx, phrase, cellW - 28);

    while (
      (ctx.measureText(line1).width > cellW - 24 ||
        (line2 && ctx.measureText(line2).width > cellW - 24)) &&
      fontSize > 14
    ) {
      fontSize -= 2;
      ctx.font = `${fontSize}px "Abaddon Bold", sans-serif`;
    }

    const ends = new Float32Array((phrase.length + 1) * 2);
    const fullW1 = ctx.measureText(line1).width;
    const startX1 = (cellW - fullW1) * 0.5;

    if (!line2) {
      for (let k = 1; k <= phrase.length; k++) {
        const u = (startX1 + ctx.measureText(line1.slice(0, k)).width) / cellW;
        ends[k * 2 + 0] = u;
        ends[k * 2 + 1] = u;
      }

      const cy = cellY + cellH * 0.5;
      ctx.lineWidth = 5;
      ctx.strokeStyle = 'rgba(0, 0, 0, 0.9)';
      ctx.strokeText(line1, cx, cy);
      ctx.fillStyle = '#ffffff';
      ctx.fillText(line1, cx, cy);
    } else {
      const fullW2 = ctx.measureText(line2).width;
      const startX2 = (cellW - fullW2) * 0.5;
      const line1FullU = (startX1 + fullW1) / cellW;

      for (let k = 1; k <= phrase.length; k++) {
        if (k <= splitIdx) {
          ends[k * 2 + 0] =
            (startX1 + ctx.measureText(line1.slice(0, k)).width) / cellW;
          ends[k * 2 + 1] = 0;
        } else {
          ends[k * 2 + 0] = line1FullU;
          const k2 = k - splitIdx - 1;
          ends[k * 2 + 1] =
            k2 > 0
              ? (startX2 + ctx.measureText(line2.slice(0, k2)).width) / cellW
              : 0;
        }
      }

      const cy1 = cellY + cellH * 0.3;
      const cy2 = cellY + cellH * 0.7;
      ctx.lineWidth = 5;
      ctx.strokeStyle = 'rgba(0, 0, 0, 0.9)';
      ctx.strokeText(line1, cx, cy1);
      ctx.strokeText(line2, cx, cy2);
      ctx.fillStyle = '#ffffff';
      ctx.fillText(line1, cx, cy1);
      ctx.fillText(line2, cx, cy2);
    }

    charEndUV.push(ends);
  }

  const texture = new THREE.CanvasTexture(canvas);
  texture.colorSpace = THREE.SRGBColorSpace;
  texture.minFilter = THREE.LinearFilter;
  texture.magFilter = THREE.LinearFilter;
  texture.generateMipmaps = false;

  return { texture, cols, rows, charEndUV };
}

async function init() {
  const font = new FontFace('Abaddon Bold', "url('/Abaddon%20Bold.ttf')");
  await font.load();
  document.fonts.add(font);

  const scene = new THREE.Scene();
  scene.background = new THREE.Color(0x000000);
  scene.fog = new THREE.Fog(0x000000, 6, 25);

  const camera = new THREE.PerspectiveCamera(
    75,
    window.innerWidth / window.innerHeight,
    0.1,
    60
  );
  camera.rotation.order = 'YXZ';

  const renderer = new THREE.WebGLRenderer({ antialias: true });
  renderer.setSize(window.innerWidth, window.innerHeight);
  renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
  renderer.outputColorSpace = THREE.SRGBColorSpace;
  document.body.appendChild(renderer.domElement);

  const textureLoader = new THREE.TextureLoader();

  const carpetTexture = textureLoader.load('/carpet.png');
  carpetTexture.wrapS = THREE.RepeatWrapping;
  carpetTexture.wrapT = THREE.RepeatWrapping;
  carpetTexture.repeat.set(GROUND_TILES, GROUND_TILES);
  carpetTexture.colorSpace = THREE.SRGBColorSpace;
  carpetTexture.anisotropy = renderer.capabilities.getMaxAnisotropy();

  const groundGeo = new THREE.PlaneGeometry(GROUND_SIZE, GROUND_SIZE);
  groundGeo.rotateX(-Math.PI / 2);
  const groundMat = new THREE.MeshStandardMaterial({
    map: carpetTexture,
    roughness: 0.95,
    metalness: 0.0,
  });
  const ground = new THREE.Mesh(groundGeo, groundMat);
  scene.add(ground);

  const wallTexture = textureLoader.load('/wall.png');
  wallTexture.wrapS = THREE.RepeatWrapping;
  wallTexture.wrapT = THREE.RepeatWrapping;
  wallTexture.repeat.set(2, 1);
  wallTexture.colorSpace = THREE.SRGBColorSpace;
  wallTexture.anisotropy = renderer.capabilities.getMaxAnisotropy();

  const wallMat = new THREE.MeshStandardMaterial({
    map: wallTexture,
    roughness: 0.9,
    metalness: 0.0,
  });

  const hWallGeo = new THREE.BoxGeometry(
    CELL_SIZE + WALL_THICKNESS,
    WALL_HEIGHT,
    WALL_THICKNESS
  );
  hWallGeo.translate(0, WALL_HEIGHT * 0.5, 0);
  const hWalls = new THREE.InstancedMesh(hWallGeo, wallMat, MAX_WALL_INSTANCES);
  hWalls.frustumCulled = false;
  scene.add(hWalls);

  const vWallGeo = new THREE.BoxGeometry(
    WALL_THICKNESS,
    WALL_HEIGHT,
    CELL_SIZE + WALL_THICKNESS
  );
  vWallGeo.translate(0, WALL_HEIGHT * 0.5, 0);
  const vWalls = new THREE.InstancedMesh(vWallGeo, wallMat, MAX_WALL_INSTANCES);
  vWalls.frustumCulled = false;
  scene.add(vWalls);

  let audioCtx = null;
  const keyBuffers = [];
  const footstepBuffers = [];
  let lastFootstepTime = 0;

  function ensureAudio() {
    if (audioCtx) {
      if (audioCtx.state === 'suspended') {
        audioCtx.resume();
      }
      return;
    }
    const Ctx = window.AudioContext || window.webkitAudioContext;
    if (!Ctx) return;
    audioCtx = new Ctx();

    fetch('/vocal-ambience.mp3')
      .then((res) => res.arrayBuffer())
      .then((buf) => audioCtx.decodeAudioData(buf))
      .then((decoded) => {
        const source = audioCtx.createBufferSource();
        source.buffer = decoded;
        source.loop = true;
        const gain = audioCtx.createGain();
        gain.gain.value = 0.18;
        source.connect(gain);
        gain.connect(audioCtx.destination);
        source.start();
      })
      .catch(() => {});

    for (let k = 1; k <= 5; k++) {
      fetch(`/key-${k}.mp3`)
        .then((res) => res.arrayBuffer())
        .then((buf) => audioCtx.decodeAudioData(buf))
        .then((decoded) => {
          keyBuffers.push(decoded);
        })
        .catch(() => {});
    }

    for (let f = 1; f <= 4; f++) {
      fetch(`/footstep-${f}.mp3`)
        .then((res) => res.arrayBuffer())
        .then((buf) => audioCtx.decodeAudioData(buf))
        .then((decoded) => {
          footstepBuffers.push(decoded);
        })
        .catch(() => {});
    }
  }

  function playRandomKeySound() {
    if (!audioCtx || keyBuffers.length === 0) return;
    const buffer = keyBuffers[Math.floor(Math.random() * keyBuffers.length)];
    const source = audioCtx.createBufferSource();
    source.buffer = buffer;
    source.connect(audioCtx.destination);
    source.start();
  }

  function playFootstepSound(dist) {
    if (!audioCtx || footstepBuffers.length === 0) return;
    const now = audioCtx.currentTime;
    if (now - lastFootstepTime < 0.09) return;
    lastFootstepTime = now;

    const buffer =
      footstepBuffers[Math.floor(Math.random() * footstepBuffers.length)];
    const source = audioCtx.createBufferSource();
    source.buffer = buffer;

    const gain = audioCtx.createGain();
    const atten = Math.pow(Math.max(0, 1 - dist / FOOTSTEP_RADIUS), 1.3);
    gain.gain.value = atten * 0.5;

    source.connect(gain);
    gain.connect(audioCtx.destination);
    source.start();
  }

  const playerLight = new THREE.PointLight(0xfff0d8, 18, 25, 1.8);
  playerLight.position.set(0, EYE_HEIGHT + 0.25, 0);
  scene.add(playerLight);

  const manTexture = textureLoader.load('/man.png');
  manTexture.colorSpace = THREE.SRGBColorSpace;

  const manGeo = new THREE.PlaneGeometry(MAN_WIDTH, MAN_HEIGHT);
  manGeo.translate(0, MAN_HEIGHT * 0.5, 0);
  const manMat = new THREE.MeshStandardMaterial({
    map: manTexture,
    alphaTest: 0.35,
    roughness: 0.9,
    metalness: 0.0,
  });

  const instancedMen = new THREE.InstancedMesh(manGeo, manMat, MAN_COUNT);
  instancedMen.frustumCulled = false;
  scene.add(instancedMen);

  const { texture: atlasTexture, cols, rows, charEndUV } = createPhraseAtlasTexture(PHRASES);
  const labelGeo = new THREE.PlaneGeometry(2.6, 0.65);
  const uvRects = new Float32Array(MAN_COUNT * 4);
  const typedUArray = new Float32Array(MAN_COUNT * 2);

  const labelMat = new THREE.ShaderMaterial({
    uniforms: THREE.UniformsUtils.merge([
      THREE.UniformsLib.fog,
      {
        uMap: { value: atlasTexture },
        uTime: { value: 0 },
        uTypePulse: { value: 0 },
      },
    ]),
    vertexShader: `
      attribute vec4 aUvRect;
      attribute vec2 aTypedU;
      varying vec2 vUv;
      varying vec4 vUvRect;
      varying float vLocalU;
      varying float vLocalV;
      varying vec2 vTypedU;
      #include <fog_pars_vertex>
      void main() {
        vUv = aUvRect.xy + uv * aUvRect.zw;
        vUvRect = aUvRect;
        vLocalU = uv.x;
        vLocalV = uv.y;
        vTypedU = aTypedU;
        vec4 mvPosition = modelViewMatrix * instanceMatrix * vec4(position, 1.0);
        gl_Position = projectionMatrix * mvPosition;
        #include <fog_vertex>
      }
    `,
    fragmentShader: `
      uniform sampler2D uMap;
      uniform float uTime;
      uniform float uTypePulse;
      varying vec2 vUv;
      varying vec4 vUvRect;
      varying float vLocalU;
      varying float vLocalV;
      varying vec2 vTypedU;
      #include <fog_pars_fragment>
      void main() {
        float lineTypedU = (vLocalV > 0.5) ? vTypedU.x : vTypedU.y;
        bool isTyped = lineTypedU > 0.0 && vLocalU <= lineTypedU;
        vec2 sampleUv = vUv;
        if (isTyped && uTypePulse > 0.01) {
          vec2 jitter = vec2(
            sin(uTime * 95.0 + vLocalU * 80.0),
            cos(uTime * 110.0 + vLocalU * 60.0)
          ) * (uTypePulse * 0.045) * vUvRect.zw;
          vec2 cellMin = vUvRect.xy;
          vec2 cellMax = vUvRect.xy + vUvRect.zw;
          sampleUv = clamp(sampleUv + jitter, cellMin, cellMax);
        }
        vec4 texel = texture2D(uMap, sampleUv);
        if (texel.a < 0.1) discard;
        if (isTyped) {
          texel.rgb *= vec3(1.0, 0.85, 0.2);
        }
        gl_FragColor = texel;
        #include <fog_fragment>
      }
    `,
    fog: true,
    transparent: true,
  });

  const men = Array.from({ length: MAN_COUNT }, (_, i) => {
    const r = 3 + Math.sqrt(Math.random()) * (SPAWN_RADIUS - 3);
    const theta = Math.random() * Math.PI * 2;
    const phraseIndex = Math.floor(Math.random() * PHRASES.length);

    const col = phraseIndex % cols;
    const row = Math.floor(phraseIndex / cols);
    const uW = 1 / cols;
    const vH = 1 / rows;
    const u0 = col * uW;
    const v0 = 1 - (row + 1) * vH;

    uvRects[i * 4 + 0] = u0;
    uvRects[i * 4 + 1] = v0;
    uvRects[i * 4 + 2] = uW;
    uvRects[i * 4 + 3] = vH;

    return {
      alive: true,
      phraseIndex,
      phrase: PHRASES[phraseIndex],
      x: Math.cos(theta) * r,
      z: Math.sin(theta) * r,
      angle: Math.random() * Math.PI * 2,
      turnRate: (Math.random() - 0.5) * 1.0,
      turnTimer: Math.random() * 3.0,
      stepTimer: Math.random() * 0.7,
      speed: 0.25 + Math.random() * 0.35,
    };
  });

  labelGeo.setAttribute('aUvRect', new THREE.InstancedBufferAttribute(uvRects, 4));
  const typedUAttr = new THREE.InstancedBufferAttribute(typedUArray, 2);
  labelGeo.setAttribute('aTypedU', typedUAttr);

  const instancedLabels = new THREE.InstancedMesh(labelGeo, labelMat, MAN_COUNT);
  instancedLabels.frustumCulled = false;
  scene.add(instancedLabels);

  const player = {
    x: 0,
    z: 0,
    yaw: 0,
    vx: 0,
    vz: 0,
    angVel: 0,
  };

  let anxiety = 0;
  let isDead = false;
  let deathTime = 0;
  let typePulse = 0;
  const anxietyHud = document.getElementById('anxiety-hud');
  const anxietyLabel = document.getElementById('anxiety-label');
  const anxietyTrack = document.getElementById('anxiety-track');
  const anxietyFill = document.getElementById('anxiety-fill');
  const vignette = document.getElementById('vignette');
  const deathScreen = document.getElementById('death-screen');

  function updateAnxietyMeter() {
    let color = '#ffffff';
    if (anxiety > 80) {
      color = '#ff3b3b';
    } else if (anxiety > 60) {
      color = '#ffd93b';
    }
    anxietyFill.style.width = `${anxiety.toFixed(2)}%`;
    anxietyFill.style.backgroundColor = color;
    anxietyTrack.style.borderColor = color;
    anxietyLabel.style.color = color;
  }

  function triggerDeath() {
    isDead = true;
    deathTime = performance.now();
    keys.clear();
    anxietyHud.style.transform = '';
    deathScreen.style.display = 'flex';
  }

  function resetGame() {
    isDead = false;
    anxiety = 0;
    typePulse = 0;
    inputBuffer = '';
    keys.clear();

    player.x = 0;
    player.z = 0;
    player.yaw = 0;
    player.vx = 0;
    player.vz = 0;
    player.angVel = 0;

    for (let i = 0; i < MAN_COUNT; i++) {
      const r = 3 + Math.sqrt(Math.random()) * (SPAWN_RADIUS - 3);
      const theta = Math.random() * Math.PI * 2;
      const m = men[i];
      m.alive = true;
      m.x = Math.cos(theta) * r;
      m.z = Math.sin(theta) * r;
      m.angle = Math.random() * Math.PI * 2;
      m.turnRate = (Math.random() - 0.5) * 1.0;
      m.turnTimer = Math.random() * 3.0;
      m.speed = 0.25 + Math.random() * 0.35;
      resolveWallCollisions(m, MAN_RADIUS, false);
    }

    lastWallCellX = Infinity;
    lastWallCellZ = Infinity;
    updateTypedHighlights();
    updateAnxietyMeter();
    vignette.style.opacity = '0';
    anxietyHud.style.transform = '';
    deathScreen.style.display = 'none';
  }

  function addAnxiety(amount) {
    if (isDead) return;
    const next = Math.min(100, anxiety + amount);
    if (next !== anxiety) {
      anxiety = next;
      updateAnxietyMeter();
      if (anxiety >= 100) {
        triggerDeath();
      }
    }
  }

  let inputBuffer = '';
  const keys = new Set();

  function hasAlivePrefixMatch(prefix) {
    for (let i = 0; i < MAN_COUNT; i++) {
      const m = men[i];
      if (m.alive && m.phrase.startsWith(prefix)) {
        return true;
      }
    }
    return false;
  }

  function updateTypedHighlights() {
    const len = inputBuffer.length;
    for (let i = 0; i < MAN_COUNT; i++) {
      const m = men[i];
      if (len > 0 && m.alive && m.phrase.startsWith(inputBuffer)) {
        const ends = charEndUV[m.phraseIndex];
        typedUArray[i * 2 + 0] = ends[len * 2 + 0];
        typedUArray[i * 2 + 1] = ends[len * 2 + 1];
      } else {
        typedUArray[i * 2 + 0] = 0;
        typedUArray[i * 2 + 1] = 0;
      }
    }
    typedUAttr.needsUpdate = true;
  }

  function deleteMatchingMan(typed) {
    let bestIdx = -1;
    let bestDistSq = Infinity;

    for (let i = 0; i < MAN_COUNT; i++) {
      const m = men[i];
      if (!m.alive || m.phrase !== typed) continue;

      const dx = m.x - player.x;
      const dz = m.z - player.z;
      const distSq = dx * dx + dz * dz;

      if (distSq < bestDistSq) {
        bestDistSq = distSq;
        bestIdx = i;
      }
    }

    if (bestIdx !== -1) {
      men[bestIdx].alive = false;
      return true;
    }
    return false;
  }

  window.addEventListener('keydown', (e) => {
    ensureAudio();

    if (isDead) {
      if (!e.repeat && performance.now() - deathTime > 300) {
        resetGame();
      }
      return;
    }

    keys.add(e.code);

    const shiftHeld =
      e.shiftKey || keys.has('ShiftLeft') || keys.has('ShiftRight');

    if (shiftHeld || e.ctrlKey || e.metaKey || e.altKey) {
      return;
    }

    if (e.code === 'Backspace') {
      e.preventDefault();
      playRandomKeySound();
      inputBuffer = '';
      updateTypedHighlights();
      return;
    }

    if (e.code === 'Space') {
      e.preventDefault();
    }

    if (e.repeat) {
      return;
    }

    if (e.key.length === 1) {
      playRandomKeySound();
      const candidate = inputBuffer + e.key.toLowerCase();
      if (hasAlivePrefixMatch(candidate)) {
        inputBuffer = candidate;
        typePulse = 1.0;
        if (deleteMatchingMan(inputBuffer)) {
          inputBuffer = '';
        }
        updateTypedHighlights();
      } else {
        addAnxiety(ANXIETY_TYPO_PENALTY);
      }
    }
  });

  window.addEventListener('pointerdown', () => {
    ensureAudio();
    if (isDead && performance.now() - deathTime > 300) {
      resetGame();
    }
  });

  window.addEventListener('keyup', (e) => {
    keys.delete(e.code);
  });

  window.addEventListener('blur', () => {
    keys.clear();
  });

  window.addEventListener('resize', () => {
    camera.aspect = window.innerWidth / window.innerHeight;
    camera.updateProjectionMatrix();
    renderer.setSize(window.innerWidth, window.innerHeight);
  });

  const dummy = new THREE.Object3D();
  const labelDummy = new THREE.Object3D();
  const wallDummy = new THREE.Object3D();
  const clock = new THREE.Clock();

  let lastWallCellX = Infinity;
  let lastWallCellZ = Infinity;

  function updateWallInstances(pgx, pgz) {
    if (pgx === lastWallCellX && pgz === lastWallCellZ) return;
    lastWallCellX = pgx;
    lastWallCellZ = pgz;

    let hCount = 0;
    let vCount = 0;

    for (let gx = pgx - WALL_VIEW_RADIUS; gx <= pgx + WALL_VIEW_RADIUS + 1; gx++) {
      for (let gz = pgz - WALL_VIEW_RADIUS; gz <= pgz + WALL_VIEW_RADIUS + 1; gz++) {
        if (hasHWall(gx, gz) && hCount < MAX_WALL_INSTANCES) {
          wallDummy.position.set((gx + 0.5) * CELL_SIZE, 0, gz * CELL_SIZE);
          wallDummy.rotation.set(0, 0, 0);
          wallDummy.scale.set(1, 1, 1);
          wallDummy.updateMatrix();
          hWalls.setMatrixAt(hCount++, wallDummy.matrix);
        }
        if (hasVWall(gx, gz) && vCount < MAX_WALL_INSTANCES) {
          wallDummy.position.set(gx * CELL_SIZE, 0, (gz + 0.5) * CELL_SIZE);
          wallDummy.rotation.set(0, 0, 0);
          wallDummy.scale.set(1, 1, 1);
          wallDummy.updateMatrix();
          vWalls.setMatrixAt(vCount++, wallDummy.matrix);
        }
      }
    }

    hWalls.count = hCount;
    vWalls.count = vCount;
    hWalls.instanceMatrix.needsUpdate = true;
    vWalls.instanceMatrix.needsUpdate = true;
  }

  for (let i = 0; i < MAN_COUNT; i++) {
    resolveWallCollisions(men[i], MAN_RADIUS, false);
  }

  function animate() {
    requestAnimationFrame(animate);

    const dt = Math.min(clock.getDelta(), 0.1);
    const elapsed = clock.elapsedTime;

    if (isDead) {
      renderer.render(scene, camera);
      return;
    }

    typePulse *= Math.exp(-16 * dt);
    if (typePulse < 0.005) typePulse = 0;
    labelMat.uniforms.uTime.value = elapsed;
    labelMat.uniforms.uTypePulse.value = typePulse;

    const anxietyNorm = anxiety / 100;
    const pulse = anxiety > 60 ? Math.sin(elapsed * 8) * 0.08 * anxietyNorm : 0;
    vignette.style.opacity = Math.min(1, Math.max(0, anxietyNorm + pulse)).toFixed(3);

    if (anxiety > 15) {
      const shakeAmp = Math.pow(anxietyNorm, 2) * 8;
      const sx = (Math.random() * 2 - 1) * shakeAmp;
      const sy = (Math.random() * 2 - 1) * shakeAmp;
      anxietyHud.style.transform = `translate(${sx.toFixed(1)}px, ${sy.toFixed(1)}px)`;
    } else {
      anxietyHud.style.transform = '';
    }

    const shiftHeld = keys.has('ShiftLeft') || keys.has('ShiftRight');
    let moveInput = 0;
    let turnInput = 0;

    if (shiftHeld) {
      moveInput = (keys.has('KeyW') ? 1 : 0) - (keys.has('KeyS') ? 1 : 0);
      turnInput = (keys.has('KeyA') ? 1 : 0) - (keys.has('KeyD') ? 1 : 0);
    }

    player.angVel += turnInput * ANG_ACCEL * dt;
    player.angVel *= Math.exp(-ANG_DAMPING * dt);
    player.yaw += player.angVel * dt;

    const fx = -Math.sin(player.yaw);
    const fz = -Math.cos(player.yaw);
    player.vx += fx * moveInput * MOVE_ACCEL * dt;
    player.vz += fz * moveInput * MOVE_ACCEL * dt;

    const linDamp = Math.exp(-MOVE_DAMPING * dt);
    player.vx *= linDamp;
    player.vz *= linDamp;

    player.x += player.vx * dt;
    player.z += player.vz * dt;
    resolveWallCollisions(player, PLAYER_RADIUS, true);

    camera.position.set(player.x, EYE_HEIGHT, player.z);
    camera.rotation.y = player.yaw;

    playerLight.position.set(player.x, EYE_HEIGHT + 0.25, player.z);

    ground.position.x = Math.floor(player.x / TILE_SIZE) * TILE_SIZE;
    ground.position.z = Math.floor(player.z / TILE_SIZE) * TILE_SIZE;

    updateWallInstances(
      Math.floor(player.x / CELL_SIZE),
      Math.floor(player.z / CELL_SIZE)
    );

    const maxDistSq = SPAWN_RADIUS * SPAWN_RADIUS;
    const closeRadiusSq = CLOSE_RADIUS * CLOSE_RADIUS;
    const footstepRadiusSq = FOOTSTEP_RADIUS * FOOTSTEP_RADIUS;
    let proximityPressure = 0;

    for (let i = 0; i < MAN_COUNT; i++) {
      const m = men[i];
      if (!m.alive) {
        dummy.scale.set(0, 0, 0);
        dummy.updateMatrix();
        instancedMen.setMatrixAt(i, dummy.matrix);
        instancedLabels.setMatrixAt(i, dummy.matrix);
        continue;
      }

      m.turnTimer -= dt;
      if (m.turnTimer <= 0) {
        m.turnRate = (Math.random() - 0.5) * 1.0;
        m.turnTimer = 1.2 + Math.random() * 3.0;
        m.speed = 0.25 + Math.random() * 0.35;
      }

      m.angle += m.turnRate * dt;
      m.x += Math.sin(m.angle) * m.speed * dt;
      m.z += Math.cos(m.angle) * m.speed * dt;
      resolveWallCollisions(m, MAN_RADIUS, false);

      let dx = m.x - player.x;
      let dz = m.z - player.z;
      let distSq = dx * dx + dz * dz;
      if (distSq > maxDistSq) {
        m.x = player.x - dx * 0.92;
        m.z = player.z - dz * 0.92;
        resolveWallCollisions(m, MAN_RADIUS, false);
        dx = m.x - player.x;
        dz = m.z - player.z;
        distSq = dx * dx + dz * dz;
      }

      if (distSq < footstepRadiusSq) {
        const dist = Math.sqrt(distSq);
        if (distSq < closeRadiusSq) {
          proximityPressure += 1 - dist / CLOSE_RADIUS;
        }
        m.stepTimer -= dt;
        if (m.stepTimer <= 0) {
          m.stepTimer = 0.5 + Math.random() * 0.35;
          playFootstepSound(dist);
        }
      }

      const billboardYaw = Math.atan2(player.x - m.x, player.z - m.z);

      dummy.position.set(m.x, 0, m.z);
      dummy.rotation.set(0, billboardYaw, 0);
      dummy.scale.set(1, 1, 1);
      dummy.updateMatrix();
      instancedMen.setMatrixAt(i, dummy.matrix);

      labelDummy.position.set(m.x, MAN_HEIGHT + 0.3, m.z);
      labelDummy.quaternion.copy(camera.quaternion);
      labelDummy.scale.set(1, 1, 1);
      labelDummy.updateMatrix();
      instancedLabels.setMatrixAt(i, labelDummy.matrix);
    }

    instancedMen.instanceMatrix.needsUpdate = true;
    instancedLabels.instanceMatrix.needsUpdate = true;

    if (proximityPressure > 0) {
      addAnxiety(Math.min(proximityPressure, 2.5) * ANXIETY_PROXIMITY_RATE * dt);
    }

    renderer.render(scene, camera);
  }

  animate();
}

init();
