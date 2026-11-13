import * as THREE from 'three';
import { GLTFLoader } from 'three/examples/jsm/loaders/GLTFLoader.js';
import { EffectComposer } from 'three/examples/jsm/postprocessing/EffectComposer.js';
import { RenderPass } from 'three/examples/jsm/postprocessing/RenderPass.js';
import { ShaderPass } from 'three/examples/jsm/postprocessing/ShaderPass.js';
import { OutputPass } from 'three/examples/jsm/postprocessing/OutputPass.js';

const TILE_SIZE = 2.5;
const GROUND_TILES = 40;
const GROUND_SIZE = TILE_SIZE * GROUND_TILES;
const CEILING_TILE_SIZE = 0.625;
const CEILING_TILES = GROUND_SIZE / CEILING_TILE_SIZE;

const MAN_WIDTH = 1.35;
const MAN_HEIGHT = 2.05;
const BOSS_WIDTH = 1.63;
const BOSS_HEIGHT = 2.45;
const MAX_IDLE_MEN = 200;
const MAX_ENCOUNTER_MEN = 4;

const EYE_HEIGHT = 1.65;
const CELL_SIZE = 4.2;
const WALL_HEIGHT = 3.6;
const WALL_THICKNESS = 0.45;
const WALL_VIEW_RADIUS = 8;
const MAX_WALL_INSTANCES = (WALL_VIEW_RADIUS * 2 + 2) * (WALL_VIEW_RADIUS * 2 + 2);

const ANXIETY_TYPO_PENALTY = 5;
const ENCOUNTER_ANXIETY_RATE = 1.4;
const POTTY_FILL_RATE = 0.18;
const POTTY_VENDING_BOOST = 4.5;
const POTTY_VENDING_DURATION = 9;

const MAZE_CHUNK_SIZE = 8;
const mazeChunks = new Map();
let worldSeed = (Math.random() * 0xffffffff) >>> 0;

function hash2D(gx, gz, seed) {
  let h =
    Math.imul(gx, 374761393) +
    Math.imul(gz, 668265263) +
    Math.imul(seed, 1442695041);
  h = (h ^ (h >>> 13)) * 1274126177;
  return ((h ^ (h >>> 16)) >>> 0) / 4294967296;
}

function createChunkRng(cx, cz) {
  let state =
    (Math.imul(cx, 374761393) ^
      Math.imul(cz, 668265263) ^
      Math.imul(worldSeed, 1442695041) ^
      0x9e3779b9) >>>
    0;
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

  for (let d = 0; d < 3; d++) {
    const bx = Math.floor(rand() * N);
    data[bx] &= ~1;
    const bz = Math.floor(rand() * N);
    data[bz * N] &= ~2;
  }

  for (let z = 1; z < N; z++) {
    for (let x = 1; x < N; x++) {
      if (rand() < 0.08) data[z * N + x] &= ~1;
      if (rand() < 0.08) data[z * N + x] &= ~2;
    }
  }

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

function canStep(gx, gz, dx, dz) {
  if (dz === -1) return !hasHWall(gx, gz);
  if (dz === 1) return !hasHWall(gx, gz + 1);
  if (dx === -1) return !hasVWall(gx, gz);
  if (dx === 1) return !hasVWall(gx + 1, gz);
  return false;
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
  'the grass really needed that rain',
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

  const labelScene = new THREE.Scene();
  labelScene.fog = scene.fog;

  const PS1_JITTER_HALF_HEIGHT = 220;
  const ps1GridUniform = {
    value: new THREE.Vector2(
      PS1_JITTER_HALF_HEIGHT * (window.innerWidth / window.innerHeight),
      PS1_JITTER_HALF_HEIGHT
    ),
  };

  function applyPs1Jitter(material) {
    if (!material || material.userData.ps1Jitter) return;
    material.userData.ps1Jitter = true;
    material.customProgramCacheKey = () => 'ps1-jitter';
    material.onBeforeCompile = (shader) => {
      shader.uniforms.uPs1Grid = ps1GridUniform;
      shader.vertexShader = `uniform vec2 uPs1Grid;\n${shader.vertexShader}`.replace(
        '#include <project_vertex>',
        `#include <project_vertex>
        if (gl_Position.w > 0.0) {
          vec4 ps1Snapped = gl_Position;
          ps1Snapped.xyz = gl_Position.xyz / gl_Position.w;
          ps1Snapped.xy = floor(uPs1Grid * ps1Snapped.xy + 0.5) / uPs1Grid;
          ps1Snapped.xyz *= gl_Position.w;
          gl_Position = ps1Snapped;
        }`
      );
    };
    material.needsUpdate = true;
  }

  const camera = new THREE.PerspectiveCamera(
    75,
    window.innerWidth / window.innerHeight,
    0.1,
    60
  );
  camera.rotation.order = 'YXZ';

  const renderer = new THREE.WebGLRenderer({ antialias: true });
  renderer.setSize(window.innerWidth, window.innerHeight);
  const pixelRatio = Math.min(window.devicePixelRatio, 2);
  renderer.setPixelRatio(pixelRatio);
  renderer.outputColorSpace = THREE.SRGBColorSpace;
  renderer.shadowMap.enabled = true;
  renderer.shadowMap.type = THREE.PCFSoftShadowMap;
  document.body.appendChild(renderer.domElement);

  const PIXEL_SIZE_CSS = 2.0;
  const composer = new EffectComposer(renderer);
  composer.setPixelRatio(pixelRatio);
  composer.setSize(window.innerWidth, window.innerHeight);

  const renderPass = new RenderPass(scene, camera);
  composer.addPass(renderPass);

  const outputPass = new OutputPass();
  composer.addPass(outputPass);

  const retroDitherShader = {
    uniforms: {
      tDiffuse: { value: null },
      uResolution: {
        value: new THREE.Vector2(
          window.innerWidth * pixelRatio,
          window.innerHeight * pixelRatio
        ),
      },
      uPixelSize: { value: PIXEL_SIZE_CSS * pixelRatio },
      uColorLevels: { value: 28.0 },
      uDitherStrength: { value: 0.75 },
    },
    vertexShader: /* glsl */ `
      varying vec2 vUv;
      void main() {
        vUv = uv;
        gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0);
      }
    `,
    fragmentShader: /* glsl */ `
      uniform sampler2D tDiffuse;
      uniform vec2 uResolution;
      uniform float uPixelSize;
      uniform float uColorLevels;
      uniform float uDitherStrength;
      varying vec2 vUv;

      float bayer4x4(vec2 cell) {
        int x = int(mod(cell.x, 4.0));
        int y = int(mod(cell.y, 4.0));
        int idx = y * 4 + x;
        if (idx == 0) return 0.0 / 16.0;
        if (idx == 1) return 8.0 / 16.0;
        if (idx == 2) return 2.0 / 16.0;
        if (idx == 3) return 10.0 / 16.0;
        if (idx == 4) return 12.0 / 16.0;
        if (idx == 5) return 4.0 / 16.0;
        if (idx == 6) return 14.0 / 16.0;
        if (idx == 7) return 6.0 / 16.0;
        if (idx == 8) return 3.0 / 16.0;
        if (idx == 9) return 11.0 / 16.0;
        if (idx == 10) return 1.0 / 16.0;
        if (idx == 11) return 9.0 / 16.0;
        if (idx == 12) return 15.0 / 16.0;
        if (idx == 13) return 7.0 / 16.0;
        if (idx == 14) return 13.0 / 16.0;
        return 5.0 / 16.0;
      }

      void main() {
        vec2 blockCoord = floor((vUv * uResolution) / uPixelSize);
        vec2 snappedUv = ((blockCoord + 0.5) * uPixelSize) / uResolution;
        snappedUv = clamp(snappedUv, vec2(0.0), vec2(1.0));

        vec4 texel = texture2D(tDiffuse, snappedUv);
        float bayer = bayer4x4(blockCoord) - 0.5;
        float levels = max(uColorLevels - 1.0, 1.0);

        vec3 dithered = texel.rgb + bayer * (uDitherStrength / levels);
        vec3 quantized = floor(clamp(dithered, 0.0, 1.0) * levels + 0.5) / levels;

        gl_FragColor = vec4(quantized, texel.a);
      }
    `,
  };

  const retroPass = new ShaderPass(retroDitherShader);
  composer.addPass(retroPass);

  const textureLoader = new THREE.TextureLoader();

  const carpetTexture = textureLoader.load('/carpet.png');
  carpetTexture.wrapS = THREE.RepeatWrapping;
  carpetTexture.wrapT = THREE.RepeatWrapping;
  carpetTexture.repeat.set(GROUND_TILES, GROUND_TILES);
  carpetTexture.colorSpace = THREE.SRGBColorSpace;
  carpetTexture.anisotropy = renderer.capabilities.getMaxAnisotropy();

  const groundGeo = new THREE.PlaneGeometry(GROUND_SIZE, GROUND_SIZE, 32, 32);
  groundGeo.rotateX(-Math.PI / 2);
  const groundMat = new THREE.MeshStandardMaterial({
    map: carpetTexture,
    roughness: 0.95,
    metalness: 0.0,
  });
  const ground = new THREE.Mesh(groundGeo, groundMat);
  ground.receiveShadow = true;
  scene.add(ground);

  const ceilingTexture = textureLoader.load('/ceiling-tile.png');
  ceilingTexture.wrapS = THREE.RepeatWrapping;
  ceilingTexture.wrapT = THREE.RepeatWrapping;
  ceilingTexture.repeat.set(CEILING_TILES, CEILING_TILES);
  ceilingTexture.colorSpace = THREE.SRGBColorSpace;
  ceilingTexture.anisotropy = renderer.capabilities.getMaxAnisotropy();

  const ceilingGeo = new THREE.PlaneGeometry(GROUND_SIZE, GROUND_SIZE, 32, 32);
  ceilingGeo.rotateX(Math.PI / 2);
  const ceilingMat = new THREE.MeshStandardMaterial({
    map: ceilingTexture,
    roughness: 0.9,
    metalness: 0.0,
  });
  const ceiling = new THREE.Mesh(ceilingGeo, ceilingMat);
  ceiling.position.y = WALL_HEIGHT;
  ceiling.receiveShadow = true;
  scene.add(ceiling);

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
  hWalls.castShadow = true;
  hWalls.receiveShadow = true;
  scene.add(hWalls);

  const vWallGeo = new THREE.BoxGeometry(
    WALL_THICKNESS,
    WALL_HEIGHT,
    CELL_SIZE + WALL_THICKNESS
  );
  vWallGeo.translate(0, WALL_HEIGHT * 0.5, 0);
  const vWalls = new THREE.InstancedMesh(vWallGeo, wallMat, MAX_WALL_INSTANCES);
  vWalls.frustumCulled = false;
  vWalls.castShadow = true;
  vWalls.receiveShadow = true;
  scene.add(vWalls);

  let audioCtx = null;
  const keyBuffers = [];
  const footstepBuffers = [];
  const laughBuffers = [];
  const greetingBuffers = [];
  let vendingBuffer = null;
  let waterPourBuffer = null;
  let flushBuffer = null;
  let lockedDoorBuffer = null;
  let elevatorOpenBuffer = null;
  let elevatorCloseBuffer = null;
  let youreFiredBuffer = null;
  let panicAttackBuffer = null;
  let runningAwayBuffer = null;
  let deepBassBuffer = null;
  let violinShriekBuffer = null;
  let heartbeatAudio = null;
  let vocalAmbienceAudio = null;
  let angryMumbleAudio = null;
  const activeAudioSources = new Set();

  function stopAllAudio() {
    for (const src of activeAudioSources) {
      try {
        src.stop();
      } catch {
        // already stopped
      }
    }
    activeAudioSources.clear();
    if (heartbeatAudio) {
      heartbeatAudio.pause();
      heartbeatAudio.currentTime = 0;
      heartbeatAudio.volume = 0;
      heartbeatAudio.playbackRate = 1.0;
    }
    if (vocalAmbienceAudio) {
      vocalAmbienceAudio.pause();
      vocalAmbienceAudio.currentTime = 0;
    }
    if (angryMumbleAudio) {
      angryMumbleAudio.pause();
      angryMumbleAudio.currentTime = 0;
      angryMumbleAudio.volume = 0;
    }
  }

  function ensureAudio() {
    if (!heartbeatAudio) {
      heartbeatAudio = new Audio('/heart-beat.mp3');
      heartbeatAudio.loop = true;
      heartbeatAudio.preservesPitch = true;
      heartbeatAudio.volume = 0;
      heartbeatAudio.playbackRate = 1.0;
      heartbeatAudio.play().catch(() => {});
    } else if (heartbeatAudio.paused) {
      heartbeatAudio.play().catch(() => {});
    }

    if (!vocalAmbienceAudio) {
      vocalAmbienceAudio = new Audio('/vocal-ambience.mp3');
      vocalAmbienceAudio.loop = true;
      vocalAmbienceAudio.volume = 0.8;
      vocalAmbienceAudio.play().catch(() => {});
    } else if (vocalAmbienceAudio.paused) {
      vocalAmbienceAudio.play().catch(() => {});
    }

    if (!angryMumbleAudio) {
      angryMumbleAudio = new Audio('/angry-mumble.mp3');
      angryMumbleAudio.loop = true;
      angryMumbleAudio.volume = 0;
      angryMumbleAudio.play().catch(() => {});
    } else if (angryMumbleAudio.paused) {
      angryMumbleAudio.play().catch(() => {});
    }

    if (audioCtx) {
      if (audioCtx.state === 'suspended') {
        audioCtx.resume();
      }
      return;
    }
    const Ctx = window.AudioContext || window.webkitAudioContext;
    if (!Ctx) return;
    audioCtx = new Ctx();

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

    fetch('/vending.mp3')
      .then((res) => res.arrayBuffer())
      .then((buf) => audioCtx.decodeAudioData(buf))
      .then((decoded) => {
        vendingBuffer = decoded;
      })
      .catch(() => {});

    fetch('/water-pour.mp3')
      .then((res) => res.arrayBuffer())
      .then((buf) => audioCtx.decodeAudioData(buf))
      .then((decoded) => {
        waterPourBuffer = decoded;
      })
      .catch(() => {});

    fetch('/flush.mp3')
      .then((res) => res.arrayBuffer())
      .then((buf) => audioCtx.decodeAudioData(buf))
      .then((decoded) => {
        flushBuffer = decoded;
      })
      .catch(() => {});

    fetch('/locked-door.mp3')
      .then((res) => res.arrayBuffer())
      .then((buf) => audioCtx.decodeAudioData(buf))
      .then((decoded) => {
        lockedDoorBuffer = decoded;
      })
      .catch(() => {});

    fetch('/elevator-open.mp3')
      .then((res) => res.arrayBuffer())
      .then((buf) => audioCtx.decodeAudioData(buf))
      .then((decoded) => {
        elevatorOpenBuffer = decoded;
      })
      .catch(() => {});

    fetch('/elevator-close.mp3')
      .then((res) => res.arrayBuffer())
      .then((buf) => audioCtx.decodeAudioData(buf))
      .then((decoded) => {
        elevatorCloseBuffer = decoded;
      })
      .catch(() => {});

    fetch('/youre-fired.mp3')
      .then((res) => res.arrayBuffer())
      .then((buf) => audioCtx.decodeAudioData(buf))
      .then((decoded) => {
        youreFiredBuffer = decoded;
      })
      .catch(() => {});

    fetch('/panic-attack.mp3')
      .then((res) => res.arrayBuffer())
      .then((buf) => audioCtx.decodeAudioData(buf))
      .then((decoded) => {
        panicAttackBuffer = decoded;
      })
      .catch(() => {});

    fetch('/running-away.mp3')
      .then((res) => res.arrayBuffer())
      .then((buf) => audioCtx.decodeAudioData(buf))
      .then((decoded) => {
        runningAwayBuffer = decoded;
      })
      .catch(() => {});

    fetch('/deep-bass.mp3')
      .then((res) => res.arrayBuffer())
      .then((buf) => audioCtx.decodeAudioData(buf))
      .then((decoded) => {
        deepBassBuffer = decoded;
      })
      .catch(() => {});

    fetch('/violin-shriek.mp3')
      .then((res) => res.arrayBuffer())
      .then((buf) => audioCtx.decodeAudioData(buf))
      .then((decoded) => {
        violinShriekBuffer = decoded;
      })
      .catch(() => {});

    for (const laughUrl of ['/male-laugh-1.mp3', '/male-laught-2.mp3']) {
      fetch(laughUrl)
        .then((res) => res.arrayBuffer())
        .then((buf) => audioCtx.decodeAudioData(buf))
        .then((decoded) => {
          laughBuffers.push(decoded);
        })
        .catch(() => {});
    }

    for (let g = 1; g <= 8; g++) {
      fetch(`/greeting-${g}.mp3`)
        .then((res) => res.arrayBuffer())
        .then((buf) => audioCtx.decodeAudioData(buf))
        .then((decoded) => {
          greetingBuffers.push(decoded);
        })
        .catch(() => {});
    }
  }

  function playBuffer(buffer, volume = 1.0, playbackRate = 1.0) {
    if (!audioCtx || !buffer) return false;
    const source = audioCtx.createBufferSource();
    source.buffer = buffer;
    source.playbackRate.value = playbackRate;
    if (volume !== 1.0) {
      const gain = audioCtx.createGain();
      gain.gain.value = volume;
      source.connect(gain);
      gain.connect(audioCtx.destination);
    } else {
      source.connect(audioCtx.destination);
    }
    activeAudioSources.add(source);
    source.onended = () => activeAudioSources.delete(source);
    source.start();
    return true;
  }

  function playRandomKeySound() {
    if (keyBuffers.length === 0) return;
    playBuffer(keyBuffers[Math.floor(Math.random() * keyBuffers.length)]);
  }

  function playRandomFootstep(volume = 0.55, playbackRate = 1.0) {
    if (footstepBuffers.length === 0) return;
    const buffer =
      footstepBuffers[Math.floor(Math.random() * footstepBuffers.length)];
    playBuffer(buffer, volume, playbackRate);
  }

  function playVendingSound(volume = 0.65) {
    playBuffer(vendingBuffer, volume);
  }

  function playWaterPourSound(volume = 0.65) {
    playBuffer(waterPourBuffer, volume);
  }

  function playFlushSound(volume = 0.65) {
    playBuffer(flushBuffer, volume);
  }

  function playLockedDoorSound(volume = 0.7) {
    playBuffer(lockedDoorBuffer, volume);
  }

  function playElevatorOpenSound(volume = 0.75) {
    playBuffer(elevatorOpenBuffer, volume);
  }

  function playElevatorCloseSound(volume = 0.75) {
    playBuffer(elevatorCloseBuffer, volume);
  }

  function playYoureFiredSound(volume = 0.85, playbackRate = 0.86) {
    playBuffer(youreFiredBuffer, volume, playbackRate);
  }

  function playPanicAttackSound(volume = 0.85) {
    playBuffer(panicAttackBuffer, volume);
  }

  function playRunningAwaySound(volume = 0.65) {
    playBuffer(runningAwayBuffer, volume);
  }

  function playDeepBass(volume = 0.35) {
    return playBuffer(deepBassBuffer, volume);
  }

  function playViolinShriek(volume = 0.7) {
    playBuffer(violinShriekBuffer, volume);
  }

  function playRandomLaugh(volume = 0.55) {
    if (laughBuffers.length === 0) return;
    const buffer =
      laughBuffers[Math.floor(Math.random() * laughBuffers.length)];
    playBuffer(buffer, volume);
  }

  function playRandomGreeting(volume = 0.75) {
    if (greetingBuffers.length === 0) return;
    const buffer =
      greetingBuffers[Math.floor(Math.random() * greetingBuffers.length)];
    playBuffer(buffer, volume);
  }

  const playerLight = new THREE.PointLight(0xfff0d8, 18, 25, 1.8);
  playerLight.position.set(0, EYE_HEIGHT + 0.25, 0);
  scene.add(playerLight);

  const manTexture = textureLoader.load('/man.png');
  manTexture.colorSpace = THREE.SRGBColorSpace;

  const manReact1Texture = textureLoader.load('/man-react-1.png');
  manReact1Texture.colorSpace = THREE.SRGBColorSpace;

  const manBackTexture = textureLoader.load('/man-back.png');
  manBackTexture.colorSpace = THREE.SRGBColorSpace;

  const manGeo = new THREE.PlaneGeometry(MAN_WIDTH, MAN_HEIGHT);
  manGeo.translate(0, MAN_HEIGHT * 0.5, 0);

  const idleManMat = new THREE.MeshStandardMaterial({
    map: manTexture,
    alphaTest: 0.35,
    roughness: 0.9,
    metalness: 0.0,
  });

  const idleMenMesh = new THREE.InstancedMesh(manGeo, idleManMat, MAX_IDLE_MEN);
  idleMenMesh.frustumCulled = false;
  scene.add(idleMenMesh);

  const bossTexture = textureLoader.load('/boss.png');
  bossTexture.colorSpace = THREE.SRGBColorSpace;

  const bossGeo = new THREE.PlaneGeometry(BOSS_WIDTH, BOSS_HEIGHT);
  bossGeo.translate(0, BOSS_HEIGHT * 0.5, 0);

  const bossMat = new THREE.MeshStandardMaterial({
    map: bossTexture,
    emissive: 0xff2a2a,
    emissiveMap: bossTexture,
    emissiveIntensity: 0.25,
    transparent: true,
    alphaTest: 0.35,
    roughness: 0.9,
    metalness: 0.0,
  });

  const bossMesh = new THREE.Mesh(bossGeo, bossMat);
  bossMesh.castShadow = false;
  bossMesh.receiveShadow = false;
  scene.add(bossMesh);

  const bossLight = new THREE.PointLight(0xff1a1a, 2.5, 8, 2.0);
  bossLight.castShadow = true;
  bossLight.shadow.mapSize.set(512, 512);
  bossLight.shadow.bias = -0.002;
  scene.add(bossLight);

  const encounterSlots = Array.from({ length: MAX_ENCOUNTER_MEN }, () => {
    const mat = new THREE.MeshStandardMaterial({
      map: manTexture,
      transparent: true,
      alphaTest: 0.05,
      opacity: 1,
      roughness: 0.9,
      metalness: 0.0,
    });
    const mesh = new THREE.Mesh(manGeo, mat);
    mesh.visible = false;
    scene.add(mesh);
    return {
      mesh,
      mat,
      alive: false,
      phraseIndex: 0,
      phrase: '',
      x: 0,
      z: 0,
      targetX: 0,
      targetZ: 0,
      labelY: MAN_HEIGHT + 0.3,
      targetLabelY: MAN_HEIGHT + 0.3,
      opacity: 0,
      reveal: 1,
      laughTimer: 0,
      leaving: false,
      leaveStepTimer: 0,
      leaveVx: 0,
      leaveVz: 0,
    };
  });

  const { texture: atlasTexture, cols, rows, charEndUV } = createPhraseAtlasTexture(PHRASES);
  const labelGeo = new THREE.PlaneGeometry(1.65, 0.42);
  const uvRects = new Float32Array(MAX_ENCOUNTER_MEN * 4);
  const typedUArray = new Float32Array(MAX_ENCOUNTER_MEN * 2);
  const prevTypedUArray = new Float32Array(MAX_ENCOUNTER_MEN * 2);
  const revealArray = new Float32Array(MAX_ENCOUNTER_MEN);
  const typoMaskArray = new Float32Array(MAX_ENCOUNTER_MEN);

  const labelMat = new THREE.ShaderMaterial({
    uniforms: THREE.UniformsUtils.merge([
      THREE.UniformsLib.fog,
      {
        uMap: { value: atlasTexture },
        uTime: { value: 0 },
        uTypePulse: { value: 0 },
        uTypoPulse: { value: 0 },
      },
    ]),
    vertexShader: `
      attribute vec4 aUvRect;
      attribute vec2 aTypedU;
      attribute vec2 aPrevTypedU;
      attribute float aReveal;
      attribute float aTypoMask;
      varying vec2 vUv;
      varying vec4 vUvRect;
      varying float vLocalU;
      varying float vLocalV;
      varying vec2 vTypedU;
      varying vec2 vPrevTypedU;
      varying float vReveal;
      varying float vTypoMask;
      #include <fog_pars_vertex>
      void main() {
        vUv = aUvRect.xy + uv * aUvRect.zw;
        vUvRect = aUvRect;
        vLocalU = uv.x;
        vLocalV = uv.y;
        vTypedU = aTypedU;
        vPrevTypedU = aPrevTypedU;
        vReveal = aReveal;
        vTypoMask = aTypoMask;
        vec4 mvPosition = modelViewMatrix * instanceMatrix * vec4(position, 1.0);
        gl_Position = projectionMatrix * mvPosition;
        #include <fog_vertex>
      }
    `,
    fragmentShader: `
      uniform sampler2D uMap;
      uniform float uTime;
      uniform float uTypePulse;
      uniform float uTypoPulse;
      varying vec2 vUv;
      varying vec4 vUvRect;
      varying float vLocalU;
      varying float vLocalV;
      varying vec2 vTypedU;
      varying vec2 vPrevTypedU;
      varying float vReveal;
      varying float vTypoMask;
      #include <fog_pars_fragment>
      void main() {
        float lineTypedU = (vLocalV > 0.5) ? vTypedU.x : vTypedU.y;
        float linePrevTypedU = (vLocalV > 0.5) ? vPrevTypedU.x : vPrevTypedU.y;
        bool isTyped = lineTypedU > 0.0 && vLocalU <= lineTypedU;
        bool isCurrentLetter = isTyped && lineTypedU > linePrevTypedU && vLocalU > linePrevTypedU;
        vec2 sampleUv = vUv;
        float revealAlpha = 1.0;
        if (vReveal < 1.0) {
          float col = floor(vLocalU * 18.0);
          float row = floor(vLocalV * 2.0);
          float cellSeed = fract(sin(dot(vec2(col, row), vec2(12.9898, 78.233))) * 43758.5453);
          float settleThreshold = 0.05 + 0.65 * cellSeed;
          if (vReveal < settleThreshold) {
            float tick = floor(uTime * 16.0);
            float randA = fract(sin(dot(vec2(col + tick, row), vec2(39.346, 11.135))) * 43758.5453);
            float randB = fract(sin(dot(vec2(col, row + tick), vec2(73.156, 52.235))) * 43758.5453);
            float scrambledLocalU = clamp(vLocalU + (randA - 0.5) * 0.16, 0.02, 0.98);
            float scrambledLocalV = clamp(vLocalV + (randB - 0.5) * 0.08, 0.05, 0.95);
            sampleUv = vUvRect.xy + vec2(scrambledLocalU, scrambledLocalV) * vUvRect.zw;
          }
          revealAlpha = smoothstep(0.0, 0.25, vReveal);
        }
        if (isCurrentLetter && uTypePulse > 0.01) {
          vec2 jitter = vec2(
            sin(uTime * 55.0 + vLocalU * 40.0),
            cos(uTime * 65.0 + vLocalU * 35.0)
          ) * (uTypePulse * 0.012) * vUvRect.zw;
          vec2 cellMin = vUvRect.xy;
          vec2 cellMax = vUvRect.xy + vUvRect.zw;
          sampleUv = clamp(sampleUv + jitter, cellMin, cellMax);
        }
        float typoAmount = uTypoPulse * vTypoMask;
        if (typoAmount > 0.01) {
          vec2 typoJitter = vec2(
            sin(uTime * 85.0 + vLocalV * 20.0),
            cos(uTime * 95.0 + vLocalU * 15.0)
          ) * (typoAmount * 0.028) * vUvRect.zw;
          vec2 cellMin = vUvRect.xy;
          vec2 cellMax = vUvRect.xy + vUvRect.zw;
          sampleUv = clamp(sampleUv + typoJitter, cellMin, cellMax);
        }
        vec4 texel = texture2D(uMap, sampleUv);
        texel.a *= revealAlpha;
        if (texel.a < 0.1) discard;
        if (isTyped) {
          texel.rgb *= vec3(1.0, 0.85, 0.2);
        }
        if (typoAmount > 0.01) {
          texel.rgb = mix(texel.rgb, vec3(1.0, 0.18, 0.18), min(1.0, typoAmount * 1.15));
        }
        gl_FragColor = texel;
        #include <fog_fragment>
      }
    `,
    fog: true,
    transparent: true,
    depthTest: false,
    depthWrite: false,
  });

  const uvRectAttr = new THREE.InstancedBufferAttribute(uvRects, 4);
  const typedUAttr = new THREE.InstancedBufferAttribute(typedUArray, 2);
  const prevTypedUAttr = new THREE.InstancedBufferAttribute(prevTypedUArray, 2);
  const revealAttr = new THREE.InstancedBufferAttribute(revealArray, 1);
  const typoMaskAttr = new THREE.InstancedBufferAttribute(typoMaskArray, 1);
  labelGeo.setAttribute('aUvRect', uvRectAttr);
  labelGeo.setAttribute('aTypedU', typedUAttr);
  labelGeo.setAttribute('aPrevTypedU', prevTypedUAttr);
  labelGeo.setAttribute('aReveal', revealAttr);
  labelGeo.setAttribute('aTypoMask', typoMaskAttr);

  const instancedLabels = new THREE.InstancedMesh(
    labelGeo,
    labelMat,
    MAX_ENCOUNTER_MEN
  );
  instancedLabels.frustumCulled = false;
  instancedLabels.renderOrder = 10;
  labelScene.add(instancedLabels);

  const clearedCells = new Set();
  const usedVendingCells = new Set();

  function hasIdleManSpawn(gx, gz) {
    if (gx === 0 && gz === 0) return false;
    return hash2D(gx, gz, (worldSeed + 77) | 0) < 0.16;
  }

  function hasIdleManAt(gx, gz) {
    if (clearedCells.has(`${gx},${gz}`)) return false;
    return hasIdleManSpawn(gx, gz);
  }

  let vendingWallOffset = CELL_SIZE * 0.5 - WALL_THICKNESS * 0.5 - 0.4;

  function getVendingPlacement(gx, gz) {
    if (gx === 0 && gz === 0) return null;
    if (hasIdleManSpawn(gx, gz)) return null;
    if (hash2D(gx, gz, (worldSeed + 313) | 0) >= 0.08) return null;

    const walls = [];
    if (hasHWall(gx, gz)) walls.push({ dx: 0, dz: -1, yaw: 0 });
    if (hasHWall(gx, gz + 1)) walls.push({ dx: 0, dz: 1, yaw: Math.PI });
    if (hasVWall(gx, gz)) walls.push({ dx: -1, dz: 0, yaw: Math.PI * 0.5 });
    if (hasVWall(gx + 1, gz)) walls.push({ dx: 1, dz: 0, yaw: -Math.PI * 0.5 });

    if (walls.length === 0) return null;
    const choice = walls[Math.floor(hash2D(gx, gz, (worldSeed + 517) | 0) * walls.length)];
    return {
      x: (gx + 0.5) * CELL_SIZE + choice.dx * vendingWallOffset,
      z: (gz + 0.5) * CELL_SIZE + choice.dz * vendingWallOffset,
      yaw: choice.yaw,
      dx: choice.dx,
      dz: choice.dz,
    };
  }

  const MAX_VENDING_INSTANCES = 24;
  const vendingPool = [];
  const vendingTexture = textureLoader.load('/vending.png');
  vendingTexture.colorSpace = THREE.SRGBColorSpace;
  vendingTexture.flipY = false;

  const vendingMat = new THREE.MeshStandardMaterial({
    map: vendingTexture,
    roughness: 0.65,
    metalness: 0.1,
  });

  const stockTexture = textureLoader.load('/stock.png');
  stockTexture.colorSpace = THREE.SRGBColorSpace;
  const noStockTexture = textureLoader.load('/no-stock.png');
  noStockTexture.colorSpace = THREE.SRGBColorSpace;

  const stockMat = new THREE.MeshStandardMaterial({
    map: stockTexture,
    roughness: 0.5,
    metalness: 0.1,
  });
  const noStockMat = new THREE.MeshStandardMaterial({
    map: noStockTexture,
    roughness: 0.5,
    metalness: 0.1,
  });
  const stockGeo = new THREE.PlaneGeometry(0.12, 0.096);

  const gltfLoader = new GLTFLoader();
  gltfLoader.load('/vending.glb', (gltf) => {
    const template = gltf.scene;
    template.traverse((child) => {
      if (child.isMesh) {
        child.material = vendingMat;
      }
    });

    const box = new THREE.Box3().setFromObject(template);
    const size = new THREE.Vector3();
    const center = new THREE.Vector3();
    box.getSize(size);
    box.getCenter(center);

    const targetHeight = 2.1;
    const scale = size.y > 0 ? targetHeight / size.y : 1;
    template.scale.setScalar(scale);

    const halfDepth = Math.min(size.x, size.z) * scale * 0.5;
    vendingWallOffset = CELL_SIZE * 0.5 - WALL_THICKNESS * 0.5 - halfDepth;

    const wrapper = new THREE.Group();
    template.position.set(
      -center.x * scale,
      -box.min.y * scale,
      -center.z * scale
    );
    wrapper.add(template);

    const stockQuad = new THREE.Mesh(stockGeo, stockMat);
    stockQuad.name = 'stockQuad';
    stockQuad.position.set(0.42, 1.86, halfDepth + 0.008);
    wrapper.add(stockQuad);

    for (let i = 0; i < MAX_VENDING_INSTANCES; i++) {
      const clone = wrapper.clone();
      clone.userData.stockQuad = clone.getObjectByName('stockQuad');
      clone.visible = false;
      scene.add(clone);
      vendingPool.push(clone);
    }
  });

  const doorWallOffset = CELL_SIZE * 0.5 - WALL_THICKNESS * 0.5 - 0.015;

  function getDoorPlacement(gx, gz) {
    if (gx === 0 && gz === 0) return null;
    if (hasIdleManSpawn(gx, gz)) return null;
    if (getVendingPlacement(gx, gz)) return null;
    if (hash2D(gx, gz, (worldSeed + 733) | 0) >= 0.06) return null;

    const walls = [];
    if (hasHWall(gx, gz)) walls.push({ dx: 0, dz: -1, yaw: 0 });
    if (hasHWall(gx, gz + 1)) walls.push({ dx: 0, dz: 1, yaw: Math.PI });
    if (hasVWall(gx, gz)) walls.push({ dx: -1, dz: 0, yaw: Math.PI * 0.5 });
    if (hasVWall(gx + 1, gz)) walls.push({ dx: 1, dz: 0, yaw: -Math.PI * 0.5 });

    if (walls.length === 0) return null;
    const choice = walls[Math.floor(hash2D(gx, gz, (worldSeed + 911) | 0) * walls.length)];
    const isWomens = hash2D(gx, gz, (worldSeed + 887) | 0) < 0.5;
    return {
      x: (gx + 0.5) * CELL_SIZE + choice.dx * doorWallOffset,
      z: (gz + 0.5) * CELL_SIZE + choice.dz * doorWallOffset,
      yaw: choice.yaw,
      dx: choice.dx,
      dz: choice.dz,
      isWomens,
    };
  }

  const MAX_DOOR_INSTANCES = 24;
  const doorPool = [];
  const woodDoorTexture = textureLoader.load('/wood-door.png');
  woodDoorTexture.colorSpace = THREE.SRGBColorSpace;
  const mensSignTexture = textureLoader.load('/mens-sign.png');
  mensSignTexture.colorSpace = THREE.SRGBColorSpace;
  const womansSignTexture = textureLoader.load('/womans-sign.png');
  womansSignTexture.colorSpace = THREE.SRGBColorSpace;

  const doorMat = new THREE.MeshStandardMaterial({
    map: woodDoorTexture,
    roughness: 0.75,
    metalness: 0.05,
    transparent: true,
    alphaTest: 0.1,
    polygonOffset: true,
    polygonOffsetFactor: -1,
    polygonOffsetUnits: -1,
  });

  const signMat = new THREE.MeshStandardMaterial({
    map: mensSignTexture,
    roughness: 0.5,
    metalness: 0.1,
    transparent: true,
    alphaTest: 0.1,
    polygonOffset: true,
    polygonOffsetFactor: -1,
    polygonOffsetUnits: -1,
  });

  const womensSignMat = new THREE.MeshStandardMaterial({
    map: womansSignTexture,
    roughness: 0.5,
    metalness: 0.1,
    transparent: true,
    alphaTest: 0.1,
    polygonOffset: true,
    polygonOffsetFactor: -1,
    polygonOffsetUnits: -1,
  });

  const doorHeight = 2.4;
  const doorWidth = doorHeight * (599 / 1362);
  const doorGeo = new THREE.PlaneGeometry(doorWidth, doorHeight);

  const signWidth = 0.28;
  const signHeight = signWidth * (174 / 129);
  const signGeo = new THREE.PlaneGeometry(signWidth, signHeight);

  for (let i = 0; i < MAX_DOOR_INSTANCES; i++) {
    const group = new THREE.Group();
    const doorMesh = new THREE.Mesh(doorGeo, doorMat);
    doorMesh.position.set(0, doorHeight * 0.5, 0);
    group.add(doorMesh);

    const signMesh = new THREE.Mesh(signGeo, signMat);
    signMesh.position.set(doorWidth * 0.5 + 0.28, 1.65, 0.002);
    group.add(signMesh);
    group.userData.signMesh = signMesh;

    group.visible = false;
    scene.add(group);
    doorPool.push(group);
  }

  const elevatorWallOffset = CELL_SIZE * 0.5 - WALL_THICKNESS * 0.5 - 0.015;
  let arrivalElevator = null;

  function getElevatorPlacement(gx, gz) {
    if (gx === 0 && gz === 0) return arrivalElevator;
    if (hasIdleManSpawn(gx, gz)) return null;
    if (getVendingPlacement(gx, gz)) return null;
    if (getDoorPlacement(gx, gz)) return null;
    if (hash2D(gx, gz, (worldSeed + 2027) | 0) >= 0.03) return null;

    const walls = [];
    if (hasHWall(gx, gz)) walls.push({ dx: 0, dz: -1, yaw: 0 });
    if (hasHWall(gx, gz + 1)) walls.push({ dx: 0, dz: 1, yaw: Math.PI });
    if (hasVWall(gx, gz)) walls.push({ dx: -1, dz: 0, yaw: Math.PI * 0.5 });
    if (hasVWall(gx + 1, gz)) walls.push({ dx: 1, dz: 0, yaw: -Math.PI * 0.5 });

    if (walls.length === 0) return null;
    const choice = walls[Math.floor(hash2D(gx, gz, (worldSeed + 2143) | 0) * walls.length)];
    return {
      x: (gx + 0.5) * CELL_SIZE + choice.dx * elevatorWallOffset,
      z: (gz + 0.5) * CELL_SIZE + choice.dz * elevatorWallOffset,
      yaw: choice.yaw,
      dx: choice.dx,
      dz: choice.dz,
    };
  }

  const MAX_ELEVATOR_INSTANCES = 12;
  const elevatorPool = [];
  const elevatorDoorsTexture = textureLoader.load('/elevator-doors.png');
  elevatorDoorsTexture.colorSpace = THREE.SRGBColorSpace;
  const elevatorButtonTexture = textureLoader.load('/elevator-button.png');
  elevatorButtonTexture.colorSpace = THREE.SRGBColorSpace;

  const elevatorMat = new THREE.MeshStandardMaterial({
    map: elevatorDoorsTexture,
    roughness: 0.55,
    metalness: 0.25,
    transparent: true,
    alphaTest: 0.1,
    polygonOffset: true,
    polygonOffsetFactor: -1,
    polygonOffsetUnits: -1,
  });

  const elevatorButtonMat = new THREE.MeshStandardMaterial({
    map: elevatorButtonTexture,
    roughness: 0.45,
    metalness: 0.2,
    transparent: true,
    alphaTest: 0.1,
    polygonOffset: true,
    polygonOffsetFactor: -1,
    polygonOffsetUnits: -1,
  });

  const elevatorHeight = 2.65;
  const elevatorWidth = elevatorHeight * (923 / 1373);
  const elevatorGeo = new THREE.PlaneGeometry(elevatorWidth, elevatorHeight);

  const elevatorButtonWidth = 0.16;
  const elevatorButtonHeight = elevatorButtonWidth * (165 / 72);
  const elevatorButtonGeo = new THREE.PlaneGeometry(elevatorButtonWidth, elevatorButtonHeight);

  for (let i = 0; i < MAX_ELEVATOR_INSTANCES; i++) {
    const group = new THREE.Group();
    const doorsMesh = new THREE.Mesh(elevatorGeo, elevatorMat);
    doorsMesh.position.set(0, elevatorHeight * 0.5, 0);
    group.add(doorsMesh);

    const buttonMesh = new THREE.Mesh(elevatorButtonGeo, elevatorButtonMat);
    buttonMesh.position.set(elevatorWidth * 0.5 + 0.22, 1.35, 0.002);
    group.add(buttonMesh);

    group.visible = false;
    scene.add(group);
    elevatorPool.push(group);
  }

  let waterCoolerWallOffset = CELL_SIZE * 0.5 - WALL_THICKNESS * 0.5 - 0.25;

  function getWaterCoolerPlacement(gx, gz) {
    if (gx === 0 && gz === 0) return null;
    if (hasIdleManSpawn(gx, gz)) return null;
    if (hash2D(gx, gz, (worldSeed + 2411) | 0) >= 0.07) return null;

    const vending = getVendingPlacement(gx, gz);
    const door = getDoorPlacement(gx, gz);
    const elevator = getElevatorPlacement(gx, gz);
    const walls = [];
    if (hasHWall(gx, gz)) walls.push({ dx: 0, dz: -1, yaw: 0 });
    if (hasHWall(gx, gz + 1)) walls.push({ dx: 0, dz: 1, yaw: Math.PI });
    if (hasVWall(gx, gz)) walls.push({ dx: -1, dz: 0, yaw: Math.PI * 0.5 });
    if (hasVWall(gx + 1, gz)) walls.push({ dx: 1, dz: 0, yaw: -Math.PI * 0.5 });

    const freeWalls = walls.filter(
      (w) =>
        !(vending && vending.dx === w.dx && vending.dz === w.dz) &&
        !(door && door.dx === w.dx && door.dz === w.dz) &&
        !(elevator && elevator.dx === w.dx && elevator.dz === w.dz)
    );
    if (freeWalls.length === 0) return null;

    const choice = freeWalls[Math.floor(hash2D(gx, gz, (worldSeed + 2539) | 0) * freeWalls.length)];
    return {
      x: (gx + 0.5) * CELL_SIZE + choice.dx * waterCoolerWallOffset,
      z: (gz + 0.5) * CELL_SIZE + choice.dz * waterCoolerWallOffset,
      yaw: choice.yaw,
      dx: choice.dx,
      dz: choice.dz,
    };
  }

  const MAX_WATER_COOLER_INSTANCES = 24;
  const waterCoolerPool = [];
  const waterCoolerTexture = textureLoader.load('/water-cooler.png');
  waterCoolerTexture.colorSpace = THREE.SRGBColorSpace;
  waterCoolerTexture.flipY = false;

  const waterCoolerMat = new THREE.MeshStandardMaterial({
    map: waterCoolerTexture,
    roughness: 0.55,
    metalness: 0.1,
  });

  gltfLoader.load('/water-cooler.glb', (gltf) => {
    const template = gltf.scene;
    template.traverse((child) => {
      if (child.isMesh) {
        child.material = waterCoolerMat;
      }
    });

    const box = new THREE.Box3().setFromObject(template);
    const size = new THREE.Vector3();
    const center = new THREE.Vector3();
    box.getSize(size);
    box.getCenter(center);

    const targetHeight = 2.1;
    const scale = size.y > 0 ? targetHeight / size.y : 1;
    template.scale.setScalar(scale);

    const halfDepth = Math.min(size.x, size.z) * scale * 0.5;
    waterCoolerWallOffset = CELL_SIZE * 0.5 - WALL_THICKNESS * 0.5 - halfDepth;

    const wrapper = new THREE.Group();
    template.position.set(
      -center.x * scale,
      -box.min.y * scale,
      -center.z * scale
    );
    wrapper.add(template);

    for (let i = 0; i < MAX_WATER_COOLER_INSTANCES; i++) {
      const clone = wrapper.clone();
      clone.visible = false;
      scene.add(clone);
      waterCoolerPool.push(clone);
    }
  });

  const posterWallOffset = CELL_SIZE * 0.5 - WALL_THICKNESS * 0.5 - 0.02;

  function getPosterPlacement(gx, gz) {
    if (gx === 0 && gz === 0) return null;
    if (hash2D(gx, gz, (worldSeed + 1093) | 0) >= 0.09) return null;

    const vending = getVendingPlacement(gx, gz);
    const door = getDoorPlacement(gx, gz);
    const elevator = getElevatorPlacement(gx, gz);
    const waterCooler = getWaterCoolerPlacement(gx, gz);
    const walls = [];
    if (hasHWall(gx, gz)) walls.push({ dx: 0, dz: -1, yaw: 0 });
    if (hasHWall(gx, gz + 1)) walls.push({ dx: 0, dz: 1, yaw: Math.PI });
    if (hasVWall(gx, gz)) walls.push({ dx: -1, dz: 0, yaw: Math.PI * 0.5 });
    if (hasVWall(gx + 1, gz)) walls.push({ dx: 1, dz: 0, yaw: -Math.PI * 0.5 });

    const freeWalls = walls.filter(
      (w) =>
        !(vending && vending.dx === w.dx && vending.dz === w.dz) &&
        !(door && door.dx === w.dx && door.dz === w.dz) &&
        !(elevator && elevator.dx === w.dx && elevator.dz === w.dz) &&
        !(waterCooler && waterCooler.dx === w.dx && waterCooler.dz === w.dz)
    );
    if (freeWalls.length === 0) return null;

    const choice = freeWalls[Math.floor(hash2D(gx, gz, (worldSeed + 1217) | 0) * freeWalls.length)];
    const posterIndex = Math.floor(hash2D(gx, gz, (worldSeed + 1361) | 0) * 4);
    return {
      x: (gx + 0.5) * CELL_SIZE + choice.dx * posterWallOffset,
      z: (gz + 0.5) * CELL_SIZE + choice.dz * posterWallOffset,
      yaw: choice.yaw,
      posterIndex,
    };
  }

  const MAX_POSTER_INSTANCES = 40;
  const posterPool = [];
  const posterMats = [1, 2, 3, 4].map((n) => {
    const tex = textureLoader.load(`/poster-${n}.png`);
    tex.colorSpace = THREE.SRGBColorSpace;
    return new THREE.MeshStandardMaterial({
      map: tex,
      roughness: 0.7,
      metalness: 0.05,
      polygonOffset: true,
      polygonOffsetFactor: -1,
      polygonOffsetUnits: -1,
    });
  });

  const posterHeight = 1.35;
  const posterWidth = posterHeight * (542 / 723);
  const posterGeo = new THREE.PlaneGeometry(posterWidth, posterHeight);

  for (let i = 0; i < MAX_POSTER_INSTANCES; i++) {
    const mesh = new THREE.Mesh(posterGeo, posterMats[0]);
    mesh.visible = false;
    scene.add(mesh);
    posterPool.push(mesh);
  }

  const plantCornerOffset = CELL_SIZE * 0.5 - WALL_THICKNESS * 0.5 - 0.62;

  function getPlantPlacement(gx, gz) {
    if (gx === 0 && gz === 0) return null;
    if (hash2D(gx, gz, (worldSeed + 1499) | 0) >= 0.13) return null;

    const corners = [];
    if (hasHWall(gx, gz) && hasVWall(gx, gz)) corners.push({ dx: -1, dz: -1 });
    if (hasHWall(gx, gz) && hasVWall(gx + 1, gz)) corners.push({ dx: 1, dz: -1 });
    if (hasHWall(gx, gz + 1) && hasVWall(gx, gz)) corners.push({ dx: -1, dz: 1 });
    if (hasHWall(gx, gz + 1) && hasVWall(gx + 1, gz)) corners.push({ dx: 1, dz: 1 });

    if (corners.length === 0) return null;
    const vending = getVendingPlacement(gx, gz);
    const waterCooler = getWaterCoolerPlacement(gx, gz);
    const filtered = corners.filter(
      (c) =>
        !(vending && (c.dx === vending.dx || c.dz === vending.dz)) &&
        !(waterCooler && (c.dx === waterCooler.dx || c.dz === waterCooler.dz))
    );
    const pool = filtered.length > 0 ? filtered : corners;
    const choice = pool[Math.floor(hash2D(gx, gz, (worldSeed + 1613) | 0) * pool.length)];
    return {
      x: (gx + 0.5) * CELL_SIZE + choice.dx * plantCornerOffset,
      z: (gz + 0.5) * CELL_SIZE + choice.dz * plantCornerOffset,
    };
  }

  const MAX_PLANT_INSTANCES = 32;
  const plantPool = [];
  const plantTexture = textureLoader.load('/plant-1.png');
  plantTexture.colorSpace = THREE.SRGBColorSpace;
  const plantMat = new THREE.MeshStandardMaterial({
    map: plantTexture,
    roughness: 0.85,
    metalness: 0.05,
    transparent: true,
    alphaTest: 0.1,
  });
  const plantHeight = 2.25;
  const plantWidth = plantHeight * (1024 / 1536);
  const plantGeo = new THREE.PlaneGeometry(plantWidth, plantHeight);
  plantGeo.translate(0, plantHeight * 0.5, 0);

  for (let i = 0; i < MAX_PLANT_INSTANCES; i++) {
    const mesh = new THREE.Mesh(plantGeo, plantMat);
    mesh.visible = false;
    scene.add(mesh);
    plantPool.push(mesh);
  }

  function getFluorescentPlacement(gx, gz) {
    if (hash2D(gx, gz, (worldSeed + 1741) | 0) >= 0.14) return null;
    return {
      x: (gx + 0.5) * CELL_SIZE,
      z: (gz + 0.5) * CELL_SIZE,
      yaw: 0,
    };
  }

  const MAX_FLUORESCENT_INSTANCES = 36;
  const fluorescentPool = [];
  const fluorescentTexture = textureLoader.load('/fluorescent-troffer.png');
  fluorescentTexture.colorSpace = THREE.SRGBColorSpace;
  fluorescentTexture.flipY = false;

  const fluorescentMat = new THREE.MeshStandardMaterial({
    map: fluorescentTexture,
    emissiveMap: fluorescentTexture,
    emissive: new THREE.Color(0xe8f6ff),
    emissiveIntensity: 1.35,
    roughness: 0.5,
    metalness: 0.1,
  });

  gltfLoader.load('/fluorescent-light.glb', (gltf) => {
    const template = gltf.scene;
    template.traverse((child) => {
      if (child.isMesh) {
        child.material = fluorescentMat;
      }
    });

    const box = new THREE.Box3().setFromObject(template);
    const size = new THREE.Vector3();
    const center = new THREE.Vector3();
    box.getSize(size);
    box.getCenter(center);

    const maxHoriz = Math.max(size.x, size.z);
    const scale = maxHoriz > 0 ? 1.6 / maxHoriz : 1;
    template.scale.setScalar(scale);

    const wrapper = new THREE.Group();
    template.position.set(
      -center.x * scale,
      -box.max.y * scale,
      -center.z * scale
    );
    wrapper.add(template);

    for (let i = 0; i < MAX_FLUORESCENT_INSTANCES; i++) {
      const clone = wrapper.clone();
      clone.visible = false;
      scene.add(clone);
      fluorescentPool.push(clone);
    }
  });

  const DIR_VECTORS = [
    [0, -1], // 0: North (-Z)
    [-1, 0], // 1: West (-X)
    [0, 1],  // 2: South (+Z)
    [1, 0],  // 3: East (+X)
  ];

  const player = {
    gx: 0,
    gz: 0,
    dir: 0,
    x: 0.5 * CELL_SIZE,
    z: 0.5 * CELL_SIZE,
    yaw: 0,
    targetYaw: 0,
  };

  let inEncounter = false;
  let encounterCellKey = '';
  let anxiety = 0;
  let potty = 0;
  let pottyVendingTimer = 0;
  let isDead = false;
  let deathTime = 0;
  let typePulse = 0;
  let typoPulse = 0;
  let inputBuffer = '';

  const anxietyHud = document.getElementById('anxiety-hud');
  const anxietyPortrait = document.getElementById('anxiety-portrait');
  const anxietyLabel = document.getElementById('anxiety-label');
  const anxietyTrack = document.getElementById('anxiety-track');
  const anxietyFill = document.getElementById('anxiety-fill');
  const pottyLabel = document.getElementById('potty-label');
  const pottyTrack = document.getElementById('potty-track');
  const pottyFill = document.getElementById('potty-fill');
  const vignette = document.getElementById('vignette');
  const fadeOverlay = document.getElementById('fade-overlay');
  const eventLogEl = document.getElementById('event-log');
  const MAX_LOG_ENTRIES = 5;

  function clearLog() {
    if (!eventLogEl) return;
    eventLogEl.innerHTML = '';
  }

  function addLog(text, color = '#e6e6e6') {
    if (!eventLogEl) return;
    const entry = document.createElement('div');
    entry.className = 'event-log-entry';
    entry.style.color = color;
    entry.textContent = `> ${text}`;
    eventLogEl.appendChild(entry);
    while (eventLogEl.children.length > MAX_LOG_ENTRIES) {
      eventLogEl.removeChild(eventLogEl.firstChild);
    }
    setTimeout(() => {
      entry.style.opacity = '0';
      setTimeout(() => {
        if (entry.parentNode === eventLogEl) {
          eventLogEl.removeChild(entry);
        }
      }, 650);
    }, 8500);
  }
  const deathScreen = document.getElementById('death-screen');
  const deathTitle = document.getElementById('death-title');
  const deathSub = document.getElementById('death-sub');
  const DEATH_SUB_TEXT = 'Press any key to continue';
  let deathTitleTimer = null;
  let deathSubTimer = null;

  function clearDeathTyping() {
    if (deathTitleTimer !== null) {
      clearInterval(deathTitleTimer);
      deathTitleTimer = null;
    }
    if (deathSubTimer !== null) {
      clearInterval(deathSubTimer);
      deathSubTimer = null;
    }
  }

  function typeIntoElement(el, text, intervalMs, playKey, onDone) {
    let idx = 0;
    el.textContent = '';
    const timer = setInterval(() => {
      idx++;
      el.textContent = text.slice(0, idx);
      if (playKey && text[idx - 1] !== ' ') {
        playRandomKeySound();
      }
      if (idx >= text.length) {
        clearInterval(timer);
        if (onDone) onDone();
      }
    }, intervalMs);
    return timer;
  }

  function startDeathTyping(titleText, titleIntervalMs = 65, subIntervalMs = 24) {
    clearDeathTyping();
    deathTitle.textContent = '';
    deathSub.textContent = '';
    deathSub.style.visibility = 'hidden';
    deathTitleTimer = typeIntoElement(deathTitle, titleText, titleIntervalMs, true, () => {
      deathTitleTimer = null;
    });
    return (subText = DEATH_SUB_TEXT) => {
      if (deathSubTimer !== null) {
        clearInterval(deathSubTimer);
      }
      deathSub.style.visibility = 'visible';
      deathSubTimer = typeIntoElement(deathSub, subText, subIntervalMs, false, () => {
        deathSubTimer = null;
      });
    };
  }

  function triggerDeath(message) {
    if (isDead) return;
    isDead = true;
    deathTime = performance.now();
    anxietyHud.style.transform = '';
    const startSub = startDeathTyping(message, 65, 24);
    startSub(DEATH_SUB_TEXT);
    deathScreen.style.display = 'flex';
  }

  function updateAnxietyMeter() {
    let color = '#ffffff';
    if (anxiety > 80) {
      color = '#ff3b3b';
    } else if (anxiety > 60) {
      color = '#ffd93b';
    }
    anxietyFill.style.width = `${anxiety.toFixed(2)}%`;
    anxietyFill.style.setProperty('--bar-color', color);
    anxietyTrack.style.borderColor = color;
    anxietyLabel.style.color = color;

    const portraitStage = Math.min(4, Math.floor(anxiety / 25) + 1);
    if (anxietyPortrait.dataset.stage !== String(portraitStage)) {
      anxietyPortrait.dataset.stage = String(portraitStage);
      anxietyPortrait.src = `/portrait-${portraitStage}.png`;
    }
  }

  function updatePottyMeter() {
    let color = '#ffffff';
    if (potty > 80) {
      color = '#ff3b3b';
    } else if (potty > 60) {
      color = '#ffd93b';
    }
    pottyFill.style.width = `${potty.toFixed(2)}%`;
    pottyFill.style.setProperty('--bar-color', color);
    pottyTrack.style.borderColor = color;
    pottyLabel.style.color = color;
  }

  function addAnxiety(amount) {
    if (isDead) return;
    const next = Math.min(100, anxiety + amount);
    if (next !== anxiety) {
      anxiety = next;
      updateAnxietyMeter();
      if (anxiety >= 100) {
        playPanicAttackSound();
        triggerDeath('You had a panic attack...');
      }
    }
  }

  function updateTypedHighlights() {
    const len = inputBuffer.length;
    for (let i = 0; i < MAX_ENCOUNTER_MEN; i++) {
      const slot = encounterSlots[i];
      if (len > 0 && slot.alive && slot.phrase.startsWith(inputBuffer)) {
        const ends = charEndUV[slot.phraseIndex];
        typedUArray[i * 2 + 0] = ends[len * 2 + 0];
        typedUArray[i * 2 + 1] = ends[len * 2 + 1];
        prevTypedUArray[i * 2 + 0] = ends[(len - 1) * 2 + 0];
        prevTypedUArray[i * 2 + 1] = ends[(len - 1) * 2 + 1];
      } else {
        typedUArray[i * 2 + 0] = 0;
        typedUArray[i * 2 + 1] = 0;
        prevTypedUArray[i * 2 + 0] = 0;
        prevTypedUArray[i * 2 + 1] = 0;
      }
    }
    typedUAttr.needsUpdate = true;
    prevTypedUAttr.needsUpdate = true;
  }

  let encounterCenterX = 0;
  let encounterCenterZ = 0;
  let encounterRx = 1;
  let encounterRz = 0;

  function arrangeEncounterSlots(snapLabelY = false) {
    const aliveSlots = encounterSlots.filter((s) => s.alive);
    const count = aliveSlots.length;
    if (count === 0) return;

    const spacing = count === 4 ? 0.85 : count === 3 ? 0.95 : 1.1;
    for (let k = 0; k < count; k++) {
      const slot = aliveSlots[k];
      const offset = (k - (count - 1) * 0.5) * spacing;
      slot.targetX = encounterCenterX + encounterRx * offset;
      slot.targetZ = encounterCenterZ + encounterRz * offset;
      slot.targetLabelY =
        count === 1
          ? MAN_HEIGHT + 0.3
          : MAN_HEIGHT + (k % 2 === 0 ? 0.24 : 0.76);
      if (snapLabelY) {
        slot.labelY = slot.targetLabelY;
      }
    }
  }

  function startEncounter(mx, mz) {
    inEncounter = true;
    encounterCellKey = `${mx},${mz}`;
    clearedCells.add(encounterCellKey);
    inputBuffer = '';

    const roll = Math.random();
    let count = 1;
    if (roll > 0.95) count = 4;
    else if (roll > 0.85) count = 3;
    else if (roll > 0.6) count = 2;
    const usedPhrases = new Set();

    const centerX = (mx + 0.5) * CELL_SIZE;
    const centerZ = (mz + 0.5) * CELL_SIZE;
    const toPlayerX = Math.sin(player.targetYaw);
    const toPlayerZ = Math.cos(player.targetYaw);
    const forwardStep = 0.85;
    encounterCenterX = centerX + toPlayerX * forwardStep;
    encounterCenterZ = centerZ + toPlayerZ * forwardStep;
    encounterRx = Math.cos(player.targetYaw);
    encounterRz = -Math.sin(player.targetYaw);
    const spacing = count === 4 ? 0.85 : count === 3 ? 0.95 : 1.1;

    for (let i = 0; i < MAX_ENCOUNTER_MEN; i++) {
      const slot = encounterSlots[i];
      if (i >= count) {
        slot.alive = false;
        slot.mesh.visible = false;
        revealArray[i] = 1;
        continue;
      }

      let phraseIndex = Math.floor(Math.random() * PHRASES.length);
      while (usedPhrases.has(phraseIndex)) {
        phraseIndex = Math.floor(Math.random() * PHRASES.length);
      }
      usedPhrases.add(phraseIndex);

      const offset = (i - (count - 1) * 0.5) * spacing;
      slot.alive = true;
      slot.leaving = false;
      slot.laughTimer = 0;
      slot.reveal = 0;
      revealArray[i] = 0;
      slot.mat.map = manTexture;
      slot.mat.needsUpdate = true;
      slot.phraseIndex = phraseIndex;
      slot.phrase = PHRASES[phraseIndex];

      if (i === 0) {
        slot.x = centerX;
        slot.z = centerZ;
        slot.opacity = 1;
      } else {
        slot.x = centerX + encounterRx * offset * 1.4;
        slot.z = centerZ + encounterRz * offset * 1.4;
        slot.opacity = 0;
      }

      slot.mat.opacity = slot.opacity;
      slot.mesh.position.set(slot.x, 0, slot.z);
      slot.mesh.visible = true;

      const col = phraseIndex % cols;
      const row = Math.floor(phraseIndex / cols);
      const uW = 1 / cols;
      const vH = 1 / rows;
      uvRects[i * 4 + 0] = col * uW;
      uvRects[i * 4 + 1] = 1 - (row + 1) * vH;
      uvRects[i * 4 + 2] = uW;
      uvRects[i * 4 + 3] = vH;
    }

    arrangeEncounterSlots(true);

    playRandomGreeting();
    if (count > 1) {
      playRandomFootstep(0.5);
      playViolinShriek();
      addLog(`${count} coworkers ambush you!`, '#ff8c66');
    } else {
      addLog('A coworker corners you for small talk.', '#ffd166');
    }

    uvRectAttr.needsUpdate = true;
    revealAttr.needsUpdate = true;
    updateTypedHighlights();
  }

  function hasEncounterPrefixMatch(prefix) {
    for (let i = 0; i < MAX_ENCOUNTER_MEN; i++) {
      const slot = encounterSlots[i];
      if (slot.alive && slot.phrase.startsWith(prefix)) {
        return true;
      }
    }
    return false;
  }

  function checkAndClearEncounterMatch(typed) {
    let matched = false;
    let remaining = 0;

    for (let i = 0; i < MAX_ENCOUNTER_MEN; i++) {
      const slot = encounterSlots[i];
      if (!slot.alive) continue;
      if (!matched && slot.phrase === typed) {
        slot.alive = false;
        slot.leaving = true;
        slot.leaveStepTimer = 0;
        slot.laughTimer = 0;
        slot.mat.map = manBackTexture;
        slot.mat.needsUpdate = true;
        const dx = slot.x - player.x;
        const dz = slot.z - player.z;
        const dist = Math.hypot(dx, dz) || 1;
        slot.leaveVx = (dx / dist) * 2.2;
        slot.leaveVz = (dz / dist) * 2.2;
        matched = true;
      } else {
        remaining++;
      }
    }

    if (matched) {
      if (remaining === 0) {
        inEncounter = false;
        inputBuffer = '';
        addLog('Escaped the conversation.', '#9be564');
      } else {
        arrangeEncounterSlots(false);
        addLog('Brushed off a coworker.', '#c8e6c9');
      }
    }
    return matched;
  }

  const nudge = {
    active: false,
    t: 0,
    duration: 0.34,
    dx: 0,
    dz: 0,
    distance: 0.32,
  };

  const vendingShake = {
    active: false,
    gx: 0,
    gz: 0,
    t: 0,
    duration: 0.55,
  };

  const waterCoolerShake = {
    active: false,
    gx: 0,
    gz: 0,
    t: 0,
    duration: 0.55,
  };

  const boss = {
    gx: 0,
    gz: 0,
    prevGx: 0,
    prevGz: 0,
    x: 0,
    z: 0,
    stepTimer: 0,
    stepInterval: 2.8,
    rumble: 0,
    sightCooldown: 0,
  };

  const bossCatch = {
    active: false,
    timer: 0,
    duration: 3.1,
    promptShown: false,
    canRestart: false,
    startSubTyping: null,
    stopX: 0,
    stopZ: 0,
  };

  function findBossSpawnCell(originGx, originGz, minDist = 6, maxDist = 9) {
    const visited = new Set([`${originGx},${originGz}`]);
    const queue = [{ gx: originGx, gz: originGz, dist: 0 }];
    const candidates = [];
    let head = 0;

    while (head < queue.length) {
      const cur = queue[head++];
      if (cur.dist >= minDist && cur.dist <= maxDist) {
        candidates.push(cur);
      }
      if (cur.dist >= maxDist) continue;
      for (const [dx, dz] of DIR_VECTORS) {
        if (!canStep(cur.gx, cur.gz, dx, dz)) continue;
        const nx = cur.gx + dx;
        const nz = cur.gz + dz;
        const key = `${nx},${nz}`;
        if (visited.has(key)) continue;
        visited.add(key);
        queue.push({ gx: nx, gz: nz, dist: cur.dist + 1 });
      }
    }

    if (candidates.length > 0) {
      return candidates[Math.floor(Math.random() * candidates.length)];
    }
    return { gx: originGx + minDist, gz: originGz };
  }

  function getNextBossStep(bx, bz, tx, tz) {
    const visited = new Map();
    const startKey = `${bx},${bz}`;
    visited.set(startKey, null);
    const queue = [{ gx: bx, gz: bz, dist: 0 }];
    let head = 0;
    let found = false;

    while (head < queue.length) {
      const cur = queue[head++];
      if (cur.gx === tx && cur.gz === tz) {
        found = true;
        break;
      }
      if (cur.dist >= 20) continue;
      for (const [dx, dz] of DIR_VECTORS) {
        if (!canStep(cur.gx, cur.gz, dx, dz)) continue;
        const nx = cur.gx + dx;
        const nz = cur.gz + dz;
        const key = `${nx},${nz}`;
        if (visited.has(key)) continue;
        visited.set(key, { gx: cur.gx, gz: cur.gz });
        queue.push({ gx: nx, gz: nz, dist: cur.dist + 1 });
      }
    }

    if (found) {
      let cx = tx;
      let cz = tz;
      while (true) {
        const parent = visited.get(`${cx},${cz}`);
        if (!parent) break;
        if (parent.gx === bx && parent.gz === bz) {
          return { gx: cx, gz: cz };
        }
        cx = parent.gx;
        cz = parent.gz;
      }
    }

    let bestStep = null;
    let bestScore = Infinity;
    for (const [dx, dz] of DIR_VECTORS) {
      if (!canStep(bx, bz, dx, dz)) continue;
      const nx = bx + dx;
      const nz = bz + dz;
      const score = Math.abs(nx - tx) + Math.abs(nz - tz);
      if (score < bestScore) {
        bestScore = score;
        bestStep = { gx: nx, gz: nz };
      }
    }
    return bestStep;
  }

  function hasLineOfSight(x1, z1, x2, z2) {
    let gx = Math.floor(x1 / CELL_SIZE);
    let gz = Math.floor(z1 / CELL_SIZE);
    const tx = Math.floor(x2 / CELL_SIZE);
    const tz = Math.floor(z2 / CELL_SIZE);
    if (gx === tx && gz === tz) return true;

    const dx = x2 - x1;
    const dz = z2 - z1;
    const stepX = dx >= 0 ? 1 : -1;
    const stepZ = dz >= 0 ? 1 : -1;

    const tDeltaX = dx === 0 ? Infinity : Math.abs(CELL_SIZE / dx);
    const tDeltaZ = dz === 0 ? Infinity : Math.abs(CELL_SIZE / dz);

    let tMaxX =
      dx === 0
        ? Infinity
        : ((stepX > 0 ? (gx + 1) * CELL_SIZE - x1 : x1 - gx * CELL_SIZE) /
            Math.abs(dx));
    let tMaxZ =
      dz === 0
        ? Infinity
        : ((stepZ > 0 ? (gz + 1) * CELL_SIZE - z1 : z1 - gz * CELL_SIZE) /
            Math.abs(dz));

    for (let iter = 0; iter < 64; iter++) {
      if (gx === tx && gz === tz) return true;
      if (tMaxX < tMaxZ) {
        if (stepX > 0 ? hasVWall(gx + 1, gz) : hasVWall(gx, gz)) return false;
        gx += stepX;
        tMaxX += tDeltaX;
      } else {
        if (stepZ > 0 ? hasHWall(gx, gz + 1) : hasHWall(gx, gz)) return false;
        gz += stepZ;
        tMaxZ += tDeltaZ;
      }
    }
    return false;
  }

  function canSeeBoss() {
    const dx = boss.x - player.x;
    const dz = boss.z - player.z;
    const dist = Math.hypot(dx, dz);
    if (dist > 22) return false;
    if (dist > 0.01) {
      const fwdX = -Math.sin(player.yaw);
      const fwdZ = -Math.cos(player.yaw);
      const dot = (dx * fwdX + dz * fwdZ) / dist;
      if (dot < 0.62) return false;
    }
    return hasLineOfSight(player.x, player.z, boss.x, boss.z);
  }

  function spawnBoss() {
    const cell = findBossSpawnCell(player.gx, player.gz, 6, 9);
    boss.gx = cell.gx;
    boss.gz = cell.gz;
    boss.prevGx = cell.gx;
    boss.prevGz = cell.gz;
    boss.x = (boss.gx + 0.5) * CELL_SIZE;
    boss.z = (boss.gz + 0.5) * CELL_SIZE;
    boss.stepTimer = 0;
    boss.rumble = 0;
    boss.sightCooldown = 0;
    bossCatch.active = false;
    bossCatch.timer = 0;
    bossCatch.promptShown = false;
    bossCatch.canRestart = false;
    bossCatch.startSubTyping = null;
    clearDeathTyping();
    bossMesh.position.set(boss.x, 0, boss.z);
    bossLight.position.set(boss.x, 1.45, boss.z);
  }

  spawnBoss();

  let floorLevel = 1;
  const elevatorTransition = {
    active: false,
    timers: [],
  };

  function clearElevatorTransition() {
    for (const id of elevatorTransition.timers) {
      clearTimeout(id);
    }
    elevatorTransition.timers.length = 0;
    elevatorTransition.active = false;
    if (fadeOverlay) {
      fadeOverlay.style.opacity = '0';
    }
  }

  function advanceToNextFloor() {
    floorLevel += 1;
    inEncounter = false;
    inputBuffer = '';
    worldSeed = (Math.random() * 0xffffffff) >>> 0;
    mazeChunks.clear();
    clearedCells.clear();
    usedVendingCells.clear();
    vendingShake.active = false;
    vendingShake.t = 0;
    waterCoolerShake.active = false;
    waterCoolerShake.t = 0;

    // Pick a direction facing out into an open corridor, ideally with a wall behind for the elevator
    let spawnDir = 0;
    let foundWithBackWall = false;
    for (let d = 0; d < 4; d++) {
      const [fdx, fdz] = DIR_VECTORS[d];
      const [bdx, bdz] = DIR_VECTORS[(d + 2) % 4];
      if (canStep(0, 0, fdx, fdz)) {
        if (!canStep(0, 0, bdx, bdz)) {
          spawnDir = d;
          foundWithBackWall = true;
          break;
        }
        if (!foundWithBackWall) {
          spawnDir = d;
        }
      }
    }

    const backDir = (spawnDir + 2) % 4;
    const [bdx, bdz] = DIR_VECTORS[backDir];
    if (!canStep(0, 0, bdx, bdz)) {
      const wallYawMap = {
        '0,-1': 0,
        '0,1': Math.PI,
        '-1,0': Math.PI * 0.5,
        '1,0': -Math.PI * 0.5,
      };
      arrivalElevator = {
        x: 0.5 * CELL_SIZE + bdx * elevatorWallOffset,
        z: 0.5 * CELL_SIZE + bdz * elevatorWallOffset,
        yaw: wallYawMap[`${bdx},${bdz}`],
        dx: bdx,
        dz: bdz,
      };
    } else {
      arrivalElevator = null;
    }

    player.gx = 0;
    player.gz = 0;
    player.dir = spawnDir;
    player.x = 0.5 * CELL_SIZE;
    player.z = 0.5 * CELL_SIZE;
    player.yaw = spawnDir * Math.PI * 0.5;
    player.targetYaw = player.yaw;

    for (let i = 0; i < MAX_ENCOUNTER_MEN; i++) {
      encounterSlots[i].alive = false;
      encounterSlots[i].leaving = false;
      encounterSlots[i].laughTimer = 0;
      encounterSlots[i].mat.map = manTexture;
      encounterSlots[i].mesh.visible = false;
    }

    lastWallCellX = Infinity;
    lastWallCellZ = Infinity;
    updateTypedHighlights();
    spawnBoss();
    addLog(`Took the elevator up to Floor ${floorLevel}.`, '#90caf9');
  }

  function triggerElevatorTransition() {
    if (elevatorTransition.active || isDead || bossCatch.active) return;
    elevatorTransition.active = true;
    playElevatorOpenSound();
    if (fadeOverlay) {
      fadeOverlay.style.opacity = '1';
    }

    const t1 = setTimeout(() => {
      advanceToNextFloor();
      playElevatorCloseSound();
      if (fadeOverlay) {
        fadeOverlay.style.opacity = '0';
      }
      const t2 = setTimeout(() => {
        elevatorTransition.active = false;
        elevatorTransition.timers.length = 0;
      }, 620);
      elevatorTransition.timers.push(t2);
    }, 650);
    elevatorTransition.timers.push(t1);
  }

  function resetGame() {
    floorLevel = 1;
    arrivalElevator = null;
    clearElevatorTransition();
    isDead = false;
    inEncounter = false;
    anxiety = 0;
    potty = 0;
    pottyVendingTimer = 0;
    typePulse = 0;
    typoPulse = 0;
    inputBuffer = '';
    worldSeed = (Math.random() * 0xffffffff) >>> 0;
    mazeChunks.clear();
    clearedCells.clear();
    usedVendingCells.clear();
    nudge.active = false;
    nudge.t = 0;
    vendingShake.active = false;
    vendingShake.t = 0;
    waterCoolerShake.active = false;
    waterCoolerShake.t = 0;
    lastLaughTime = 0;

    player.gx = 0;
    player.gz = 0;
    player.dir = 0;
    player.x = 0.5 * CELL_SIZE;
    player.z = 0.5 * CELL_SIZE;
    player.yaw = 0;
    player.targetYaw = 0;

    for (let i = 0; i < MAX_ENCOUNTER_MEN; i++) {
      encounterSlots[i].alive = false;
      encounterSlots[i].leaving = false;
      encounterSlots[i].laughTimer = 0;
      encounterSlots[i].mat.map = manTexture;
      encounterSlots[i].mesh.visible = false;
    }
    stopAllAudio();

    lastWallCellX = Infinity;
    lastWallCellZ = Infinity;
    updateTypedHighlights();
    updateAnxietyMeter();
    updatePottyMeter();
    vignette.style.opacity = '0';
    anxietyHud.style.transform = '';
    deathScreen.style.display = 'none';
    deathScreen.style.backgroundColor = 'rgba(0, 0, 0, 0.92)';
    deathSub.style.visibility = 'visible';
    playerLight.intensity = 18;
    scene.fog.near = 6;
    scene.fog.far = 25;
    bossLight.intensity = 2.5;
    bossLight.distance = 8;
    bossMat.emissiveIntensity = 0.25;
    spawnBoss();
    clearLog();
    addLog('Clocked in. Avoid small talk.', '#b0bec5');
  }

  let lastLaughTime = 0;

  function triggerRandomManLaugh() {
    const now = performance.now();
    if (now - lastLaughTime < 900) return;
    if (Math.random() >= 0.16) return;

    const aliveSlots = encounterSlots.filter((s) => s.alive);
    if (aliveSlots.length === 0) return;

    lastLaughTime = now;
    playRandomLaugh();
    const chosen = aliveSlots[Math.floor(Math.random() * aliveSlots.length)];
    chosen.laughTimer = 0.85;
    chosen.mat.map = manReact1Texture;
    chosen.mat.needsUpdate = true;
  }

  window.addEventListener('keydown', (e) => {
    ensureAudio();

    if (isDead) {
      if (!e.repeat && performance.now() - deathTime > 300) {
        resetGame();
      }
      return;
    }

    if (bossCatch.active) {
      if (!e.repeat && bossCatch.canRestart) {
        resetGame();
      }
      return;
    }

    if (elevatorTransition.active) {
      return;
    }

    if (!inEncounter) {
      if (e.repeat) return;

      if (e.code === 'KeyA') {
        player.dir = (player.dir + 1) % 4;
        player.targetYaw += Math.PI * 0.5;
      } else if (e.code === 'KeyD') {
        player.dir = (player.dir + 3) % 4;
        player.targetYaw -= Math.PI * 0.5;
      } else if (e.code === 'KeyW' || e.code === 'KeyS') {
        const sign = e.code === 'KeyW' ? 1 : -1;
        const [dx, dz] = DIR_VECTORS[player.dir];
        const stepX = dx * sign;
        const stepZ = dz * sign;

        if (sign === 1) {
          const cellKey = `${player.gx},${player.gz}`;
          const placement = getVendingPlacement(player.gx, player.gz);
          if (placement && placement.dx === dx && placement.dz === dz) {
            nudge.active = true;
            nudge.t = 0;
            nudge.dx = dx;
            nudge.dz = dz;
            nudge.distance = 0.32;
            if (!usedVendingCells.has(cellKey)) {
              usedVendingCells.add(cellKey);
              anxiety = Math.max(0, anxiety - 40);
              pottyVendingTimer = POTTY_VENDING_DURATION;
              updateAnxietyMeter();
              playVendingSound();
              vendingShake.active = true;
              vendingShake.gx = player.gx;
              vendingShake.gz = player.gz;
              vendingShake.t = 0;
              addLog('Grabbed a cold drink. (-40 Anxiety, +Potty)', '#80deea');
            } else {
              addLog('The vending machine is out of stock.', '#90a4ae');
            }
            return;
          }

          const doorPlacement = getDoorPlacement(player.gx, player.gz);
          if (doorPlacement && doorPlacement.dx === dx && doorPlacement.dz === dz) {
            if (doorPlacement.isWomens) {
              nudge.active = true;
              nudge.t = 0;
              nudge.dx = dx;
              nudge.dz = dz;
              nudge.distance = 0.16;
              playLockedDoorSound();
              addLog("Locked. That's the women's restroom.", '#ffab91');
              return;
            }
            nudge.active = true;
            nudge.t = 0;
            nudge.dx = dx;
            nudge.dz = dz;
            nudge.distance = 0.32;
            potty = 0;
            pottyVendingTimer = 0;
            updatePottyMeter();
            playFlushSound();
            addLog("Relieved yourself in the men's room.", '#a5d6a7');
            return;
          }

          const waterCoolerPlacement = getWaterCoolerPlacement(player.gx, player.gz);
          if (
            waterCoolerPlacement &&
            waterCoolerPlacement.dx === dx &&
            waterCoolerPlacement.dz === dz
          ) {
            nudge.active = true;
            nudge.t = 0;
            nudge.dx = dx;
            nudge.dz = dz;
            nudge.distance = 0.32;
            playWaterPourSound();
            waterCoolerShake.active = true;
            waterCoolerShake.gx = player.gx;
            waterCoolerShake.gz = player.gz;
            waterCoolerShake.t = 0;
            addLog('Got a cup of water.', '#80deea');
            return;
          }

          const elevatorPlacement = getElevatorPlacement(player.gx, player.gz);
          if (elevatorPlacement && elevatorPlacement.dx === dx && elevatorPlacement.dz === dz) {
            nudge.active = true;
            nudge.t = 0;
            nudge.dx = dx;
            nudge.dz = dz;
            nudge.distance = 0.28;
            triggerElevatorTransition();
            return;
          }
        }

        if (canStep(player.gx, player.gz, stepX, stepZ)) {
          const nx = player.gx + stepX;
          const nz = player.gz + stepZ;
          if (nx === boss.gx && nz === boss.gz) {
            triggerBossCatch();
            return;
          }
          if (hasIdleManAt(nx, nz)) {
            if (sign === -1) {
              player.dir = (player.dir + 2) % 4;
              player.targetYaw += Math.PI;
            }
            nudge.active = true;
            nudge.t = 0;
            nudge.dx = stepX;
            nudge.dz = stepZ;
            nudge.distance = 0.16;
            startEncounter(nx, nz);
          } else {
            player.gx = nx;
            player.gz = nz;
            playRandomFootstep(0.58);
          }
        } else {
          nudge.active = true;
          nudge.t = 0;
          nudge.dx = stepX;
          nudge.dz = stepZ;
          nudge.distance = 0.16;
        }
      }
      return;
    }

    if (e.ctrlKey || e.metaKey || e.altKey) {
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
      return;
    }

    if (e.repeat) {
      return;
    }

    if (e.key.length === 1) {
      playRandomKeySound();
      const ch = e.key.toLowerCase();
      let candidate = inputBuffer + ch;
      let matched = hasEncounterPrefixMatch(candidate);

      if (!matched && inputBuffer.length > 0) {
        const withSpace = `${inputBuffer} ${ch}`;
        if (hasEncounterPrefixMatch(withSpace)) {
          candidate = withSpace;
          matched = true;
        }
      }

      if (matched) {
        inputBuffer = candidate;
        typePulse = 1.0;
        if (checkAndClearEncounterMatch(inputBuffer)) {
          inputBuffer = '';
        }
        updateTypedHighlights();
      } else {
        typoPulse = 1.0;
        for (let i = 0; i < MAX_ENCOUNTER_MEN; i++) {
          const slot = encounterSlots[i];
          typoMaskArray[i] =
            slot.alive && (inputBuffer.length === 0 || slot.phrase.startsWith(inputBuffer))
              ? 1
              : 0;
        }
        typoMaskAttr.needsUpdate = true;
        addAnxiety(ANXIETY_TYPO_PENALTY);
      }
      triggerRandomManLaugh();
    }
  });

  window.addEventListener('pointerdown', () => {
    ensureAudio();
    if (
      (isDead && performance.now() - deathTime > 300) ||
      (bossCatch.active && bossCatch.canRestart)
    ) {
      resetGame();
    }
  });

  window.addEventListener('resize', () => {
    const pr = Math.min(window.devicePixelRatio, 2);
    const aspect = window.innerWidth / window.innerHeight;
    camera.aspect = aspect;
    camera.updateProjectionMatrix();
    ps1GridUniform.value.set(
      PS1_JITTER_HALF_HEIGHT * aspect,
      PS1_JITTER_HALF_HEIGHT
    );
    renderer.setPixelRatio(pr);
    renderer.setSize(window.innerWidth, window.innerHeight);
    composer.setPixelRatio(pr);
    composer.setSize(window.innerWidth, window.innerHeight);
    retroPass.uniforms.uResolution.value.set(
      window.innerWidth * pr,
      window.innerHeight * pr
    );
    retroPass.uniforms.uPixelSize.value = PIXEL_SIZE_CSS * pr;
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

  function triggerBossCatch() {
    if (bossCatch.active || isDead) return;
    bossCatch.active = true;
    bossCatch.timer = 0;
    bossCatch.promptShown = false;
    bossCatch.canRestart = false;
    bossCatch.startSubTyping = null;
    clearDeathTyping();
    addLog('Your boss caught up to you...', '#ff5252');
    playYoureFiredSound();
    let dx = boss.x - player.x;
    let dz = boss.z - player.z;
    let len = Math.hypot(dx, dz);
    if (len < 0.05) {
      dx = boss.prevGx - player.gx;
      dz = boss.prevGz - player.gz;
      len = Math.hypot(dx, dz);
    }
    if (len < 0.05) {
      dx = -Math.sin(player.yaw);
      dz = -Math.cos(player.yaw);
      len = 1;
    }
    const dirX = dx / len;
    const dirZ = dz / len;
    bossCatch.stopX = player.x + dirX * 1.15;
    bossCatch.stopZ = player.z + dirZ * 1.15;

    const lookYaw = Math.atan2(-dirX, -dirZ);
    let diff = ((lookYaw - player.yaw + Math.PI) % (Math.PI * 2)) - Math.PI;
    if (diff < -Math.PI) diff += Math.PI * 2;
    player.targetYaw = player.yaw + diff;
    boss.rumble = Math.max(boss.rumble, 0.055);
  }

  function renderFrame() {
    renderer.autoClear = true;
    composer.render();
    renderer.autoClear = false;
    renderer.render(labelScene, camera);
    renderer.autoClear = true;
  }

  function animate() {
    requestAnimationFrame(animate);

    const dt = Math.min(clock.getDelta(), 0.1);
    const elapsed = clock.elapsedTime;

    if (isDead) {
      if (heartbeatAudio) {
        heartbeatAudio.volume = 0;
      }
      if (angryMumbleAudio) {
        angryMumbleAudio.volume = 0;
      }
      renderFrame();
      return;
    }

    typePulse *= Math.exp(-16 * dt);
    if (typePulse < 0.005) typePulse = 0;
    typoPulse *= Math.exp(-12 * dt);
    if (typoPulse < 0.005) typoPulse = 0;
    labelMat.uniforms.uTime.value = elapsed;
    labelMat.uniforms.uTypePulse.value = typePulse;
    labelMat.uniforms.uTypoPulse.value = typoPulse;

    if (!bossCatch.active && !isDead && !elevatorTransition.active) {
      let pottyRate = POTTY_FILL_RATE;
      if (pottyVendingTimer > 0) {
        pottyVendingTimer = Math.max(0, pottyVendingTimer - dt);
        pottyRate += POTTY_VENDING_BOOST;
      }
      potty = Math.min(100, potty + pottyRate * dt);
      updatePottyMeter();
      if (potty >= 100) {
        playPanicAttackSound();
        triggerDeath('You had a panic attack...');
      }
    }

    const anxietyNorm = anxiety / 100;
    const bossDistTiles = Math.hypot(boss.gx - player.gx, boss.gz - player.gz);
    const bossProx = Math.max(0, 1 - bossDistTiles / 8);
    if (heartbeatAudio) {
      const hbNorm = Math.max(0, (anxietyNorm - 0.3) / 0.7);
      const effectiveHb = Math.min(1, Math.max(hbNorm, bossProx * 0.92));
      heartbeatAudio.volume =
        effectiveHb > 0 ? Math.pow(effectiveHb, 1.8) * 0.42 : 0;
      heartbeatAudio.playbackRate = 1.0 + Math.pow(effectiveHb, 1.6) * 0.65;
    }
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

    const targetX = (player.gx + 0.5) * CELL_SIZE;
    const targetZ = (player.gz + 0.5) * CELL_SIZE;
    const moveLerp = 1 - Math.exp(-7.5 * dt);
    const rotLerp = 1 - Math.exp(-16 * dt);

    player.x += (targetX - player.x) * moveLerp;
    player.z += (targetZ - player.z) * moveLerp;
    player.yaw += (player.targetYaw - player.yaw) * rotLerp;

    let nudgeX = 0;
    let nudgeZ = 0;
    if (nudge.active) {
      nudge.t += dt;
      const u = Math.min(1, nudge.t / nudge.duration);
      const split = 0.35;
      const offset =
        u < split
          ? Math.sin((u / split) * Math.PI * 0.5)
          : 0.5 * (1 + Math.cos(((u - split) / (1 - split)) * Math.PI));
      nudgeX = nudge.dx * nudge.distance * offset;
      nudgeZ = nudge.dz * nudge.distance * offset;
      if (nudge.t >= nudge.duration) {
        nudge.active = false;
      }
    }

    if (bossCatch.active) {
      bossCatch.timer += dt;
      const darkLerp = 1 - Math.exp(-10 * dt);
      playerLight.intensity += (0 - playerLight.intensity) * darkLerp;
      scene.fog.near += (1.2 - scene.fog.near) * darkLerp;
      scene.fog.far += (4.0 - scene.fog.far) * darkLerp;
      const flicker = 0.88 + 0.12 * Math.sin(elapsed * 42.0) * Math.cos(elapsed * 19.0);
      bossLight.intensity += (6.0 * flicker - bossLight.intensity) * darkLerp;
      bossLight.distance += (6.0 - bossLight.distance) * darkLerp;
      bossMat.emissiveIntensity += (0.85 - bossMat.emissiveIntensity) * darkLerp;

      if (!bossCatch.promptShown && bossCatch.timer >= 0.45) {
        bossCatch.promptShown = true;
        bossCatch.startSubTyping = startDeathTyping('You got fired...', 65, 24);
        deathScreen.style.backgroundColor = 'rgba(0, 0, 0, 0)';
        deathScreen.style.display = 'flex';
      }

      if (!bossCatch.canRestart && bossCatch.timer >= 1.45) {
        bossCatch.canRestart = true;
        if (bossCatch.startSubTyping) {
          bossCatch.startSubTyping();
        }
      }

      if (bossCatch.timer >= bossCatch.duration) {
        bossCatch.active = false;
        deathScreen.style.backgroundColor = 'rgba(0, 0, 0, 0.96)';
        isDead = true;
        deathTime = performance.now();
        anxietyHud.style.transform = '';
      }
    } else if (!elevatorTransition.active) {
      boss.stepTimer += dt;
      if (boss.stepTimer >= boss.stepInterval) {
        boss.stepTimer -= boss.stepInterval;
        const distBefore = Math.hypot(boss.gx - player.gx, boss.gz - player.gz);
        if (distBefore > 16) {
          const cell = findBossSpawnCell(player.gx, player.gz, 7, 10);
          boss.prevGx = cell.gx;
          boss.prevGz = cell.gz;
          boss.gx = cell.gx;
          boss.gz = cell.gz;
          boss.x = (boss.gx + 0.5) * CELL_SIZE;
          boss.z = (boss.gz + 0.5) * CELL_SIZE;
        } else {
          const next = getNextBossStep(boss.gx, boss.gz, player.gx, player.gz);
          if (next) {
            boss.prevGx = boss.gx;
            boss.prevGz = boss.gz;
            boss.gx = next.gx;
            boss.gz = next.gz;
          }
        }

        const distTiles = Math.hypot(boss.gx - player.gx, boss.gz - player.gz);
        if (distTiles <= 8) {
          const prox = Math.max(0, 1 - distTiles / 8);
          playRandomFootstep(Math.min(1.0, 0.3 + prox * 0.9), 0.65);
          boss.rumble = Math.max(boss.rumble, 0.015 + Math.pow(prox, 2.4) * 0.14);
        }
      }

      if (boss.gx === player.gx && boss.gz === player.gz) {
        triggerBossCatch();
      }
    }

    boss.rumble *= Math.exp(-12 * dt);
    if (boss.rumble < 0.001) boss.rumble = 0;

    const bossTargetX = bossCatch.active
      ? bossCatch.stopX
      : (boss.gx + 0.5) * CELL_SIZE;
    const bossTargetZ = bossCatch.active
      ? bossCatch.stopZ
      : (boss.gz + 0.5) * CELL_SIZE;
    const bossLerp = 1 - Math.exp(-(bossCatch.active ? 10 : 2.2) * dt);
    boss.x += (bossTargetX - boss.x) * bossLerp;
    boss.z += (bossTargetZ - boss.z) * bossLerp;
    const bossMoveDist = Math.hypot(bossTargetX - boss.x, bossTargetZ - boss.z);
    const bossBounceAmp = Math.min(1, bossMoveDist / 0.35) * 0.14;
    const bossBounceY = Math.abs(Math.sin(elapsed * 20)) * bossBounceAmp;
    const bossYaw = Math.atan2(player.x - boss.x, player.z - boss.z);
    bossMesh.position.set(boss.x, bossBounceY, boss.z);
    bossMesh.rotation.set(0, bossYaw, 0);
    bossLight.position.set(
      boss.x - Math.sin(bossYaw) * 0.15,
      1.45 + bossBounceY * 0.5,
      boss.z - Math.cos(bossYaw) * 0.15
    );

    if (angryMumbleAudio) {
      const dx = boss.x - player.x;
      const dz = boss.z - player.z;
      const bossDist = Math.hypot(dx, dz);
      const maxMumbleDist = CELL_SIZE * 4.5;
      const mumbleProx = Math.max(0, 1 - bossDist / maxMumbleDist);
      const lookDot =
        bossDist > 0.001
          ? (-Math.sin(player.yaw) * dx + -Math.cos(player.yaw) * dz) / bossDist
          : 1;
      const lookFactor = 0.25 + 0.75 * ((Math.max(-1, Math.min(1, lookDot)) + 1) * 0.5);
      angryMumbleAudio.volume = Math.min(
        0.85,
        Math.pow(mumbleProx, 1.5) * 0.85 * lookFactor
      );
    }

    if (boss.sightCooldown > 0) {
      boss.sightCooldown = Math.max(0, boss.sightCooldown - dt);
    }
    if (boss.sightCooldown === 0 && canSeeBoss()) {
      if (playDeepBass()) {
        boss.sightCooldown = 12;
      }
    }

    const shakeAmp = bossCatch.active ? Math.max(boss.rumble, 0.055) : boss.rumble;
    const rumbleX = (Math.random() * 2 - 1) * shakeAmp;
    const rumbleY = (Math.random() * 2 - 1) * shakeAmp;
    const rumbleZ = (Math.random() * 2 - 1) * shakeAmp;

    camera.position.set(
      player.x + nudgeX + rumbleX,
      EYE_HEIGHT + rumbleY,
      player.z + nudgeZ + rumbleZ
    );
    camera.rotation.y = player.yaw;
    camera.rotation.z = shakeAmp > 0 ? (Math.random() * 2 - 1) * shakeAmp * 0.25 : 0;

    playerLight.position.set(player.x + nudgeX, EYE_HEIGHT + 0.25, player.z + nudgeZ);

    ground.position.x = Math.floor(player.x / TILE_SIZE) * TILE_SIZE;
    ground.position.z = Math.floor(player.z / TILE_SIZE) * TILE_SIZE;
    ceiling.position.x = Math.floor(player.x / CEILING_TILE_SIZE) * CEILING_TILE_SIZE;
    ceiling.position.z = Math.floor(player.z / CEILING_TILE_SIZE) * CEILING_TILE_SIZE;

    updateWallInstances(player.gx, player.gz);

    let idleCount = 0;
    for (let gx = player.gx - WALL_VIEW_RADIUS; gx <= player.gx + WALL_VIEW_RADIUS; gx++) {
      for (let gz = player.gz - WALL_VIEW_RADIUS; gz <= player.gz + WALL_VIEW_RADIUS; gz++) {
        if (!hasIdleManAt(gx, gz) || idleCount >= MAX_IDLE_MEN) continue;
        const mx = (gx + 0.5) * CELL_SIZE;
        const mz = (gz + 0.5) * CELL_SIZE;
        const billboardYaw = Math.atan2(player.x - mx, player.z - mz);
        dummy.position.set(mx, 0, mz);
        dummy.rotation.set(0, billboardYaw, 0);
        dummy.scale.set(1, 1, 1);
        dummy.updateMatrix();
        idleMenMesh.setMatrixAt(idleCount++, dummy.matrix);
      }
    }
    idleMenMesh.count = idleCount;
    idleMenMesh.instanceMatrix.needsUpdate = true;

    if (vendingShake.active) {
      vendingShake.t += dt;
      if (vendingShake.t >= vendingShake.duration) {
        vendingShake.active = false;
      }
    }
    if (waterCoolerShake.active) {
      waterCoolerShake.t += dt;
      if (waterCoolerShake.t >= waterCoolerShake.duration) {
        waterCoolerShake.active = false;
      }
    }

    const getShakeOffsets = (shake, gx, gz) => {
      if (!shake.active || shake.gx !== gx || shake.gz !== gz) {
        return { sx: 0, sz: 0, rx: 0, rz: 0 };
      }
      const decay = Math.pow(Math.max(0, 1 - shake.t / shake.duration), 1.4);
      return {
        sx: Math.sin(shake.t * 58) * 0.04 * decay,
        sz: Math.cos(shake.t * 47) * 0.04 * decay,
        rx: Math.sin(shake.t * 52) * 0.045 * decay,
        rz: Math.cos(shake.t * 61) * 0.045 * decay,
      };
    };

    let vendingCount = 0;
    if (vendingPool.length > 0) {
      for (let gx = player.gx - WALL_VIEW_RADIUS; gx <= player.gx + WALL_VIEW_RADIUS; gx++) {
        for (let gz = player.gz - WALL_VIEW_RADIUS; gz <= player.gz + WALL_VIEW_RADIUS; gz++) {
          if (vendingCount >= vendingPool.length) break;
          const placement = getVendingPlacement(gx, gz);
          if (!placement) continue;
          const vm = vendingPool[vendingCount++];
          const { sx, sz, rx, rz } = getShakeOffsets(vendingShake, gx, gz);
          vm.position.set(placement.x + sx, 0, placement.z + sz);
          vm.rotation.set(rx, placement.yaw, rz);
          if (vm.userData.stockQuad) {
            vm.userData.stockQuad.material = usedVendingCells.has(`${gx},${gz}`)
              ? noStockMat
              : stockMat;
          }
          vm.visible = true;
        }
      }
      for (let v = vendingCount; v < vendingPool.length; v++) {
        vendingPool[v].visible = false;
      }
    }

    let doorCount = 0;
    for (let gx = player.gx - WALL_VIEW_RADIUS; gx <= player.gx + WALL_VIEW_RADIUS; gx++) {
      for (let gz = player.gz - WALL_VIEW_RADIUS; gz <= player.gz + WALL_VIEW_RADIUS; gz++) {
        if (doorCount >= doorPool.length) break;
        const doorPlacement = getDoorPlacement(gx, gz);
        if (!doorPlacement) continue;
        const dm = doorPool[doorCount++];
        dm.position.set(doorPlacement.x, 0, doorPlacement.z);
        dm.rotation.set(0, doorPlacement.yaw, 0);
        if (dm.userData.signMesh) {
          dm.userData.signMesh.material = doorPlacement.isWomens ? womensSignMat : signMat;
        }
        dm.visible = true;
      }
    }
    for (let d = doorCount; d < doorPool.length; d++) {
      doorPool[d].visible = false;
    }

    let elevatorCount = 0;
    for (let gx = player.gx - WALL_VIEW_RADIUS; gx <= player.gx + WALL_VIEW_RADIUS; gx++) {
      for (let gz = player.gz - WALL_VIEW_RADIUS; gz <= player.gz + WALL_VIEW_RADIUS; gz++) {
        if (elevatorCount >= elevatorPool.length) break;
        const elPlacement = getElevatorPlacement(gx, gz);
        if (!elPlacement) continue;
        const elm = elevatorPool[elevatorCount++];
        elm.position.set(elPlacement.x, 0, elPlacement.z);
        elm.rotation.set(0, elPlacement.yaw, 0);
        elm.visible = true;
      }
    }
    for (let eIdx = elevatorCount; eIdx < elevatorPool.length; eIdx++) {
      elevatorPool[eIdx].visible = false;
    }

    let waterCoolerCount = 0;
    if (waterCoolerPool.length > 0) {
      for (let gx = player.gx - WALL_VIEW_RADIUS; gx <= player.gx + WALL_VIEW_RADIUS; gx++) {
        for (let gz = player.gz - WALL_VIEW_RADIUS; gz <= player.gz + WALL_VIEW_RADIUS; gz++) {
          if (waterCoolerCount >= waterCoolerPool.length) break;
          const wcPlacement = getWaterCoolerPlacement(gx, gz);
          if (!wcPlacement) continue;
          const wcm = waterCoolerPool[waterCoolerCount++];
          const { sx, sz, rx, rz } = getShakeOffsets(waterCoolerShake, gx, gz);
          wcm.position.set(wcPlacement.x + sx, 0, wcPlacement.z + sz);
          wcm.rotation.set(rx, wcPlacement.yaw, rz);
          wcm.visible = true;
        }
      }
      for (let wc = waterCoolerCount; wc < waterCoolerPool.length; wc++) {
        waterCoolerPool[wc].visible = false;
      }
    }

    let posterCount = 0;
    for (let gx = player.gx - WALL_VIEW_RADIUS; gx <= player.gx + WALL_VIEW_RADIUS; gx++) {
      for (let gz = player.gz - WALL_VIEW_RADIUS; gz <= player.gz + WALL_VIEW_RADIUS; gz++) {
        if (posterCount >= posterPool.length) break;
        const posterPlacement = getPosterPlacement(gx, gz);
        if (!posterPlacement) continue;
        const pm = posterPool[posterCount++];
        pm.position.set(posterPlacement.x, 1.85, posterPlacement.z);
        pm.rotation.set(0, posterPlacement.yaw, 0);
        pm.material = posterMats[posterPlacement.posterIndex];
        pm.visible = true;
      }
    }
    for (let p = posterCount; p < posterPool.length; p++) {
      posterPool[p].visible = false;
    }

    let plantCount = 0;
    for (let gx = player.gx - WALL_VIEW_RADIUS; gx <= player.gx + WALL_VIEW_RADIUS; gx++) {
      for (let gz = player.gz - WALL_VIEW_RADIUS; gz <= player.gz + WALL_VIEW_RADIUS; gz++) {
        if (plantCount >= plantPool.length) break;
        const plantPlacement = getPlantPlacement(gx, gz);
        if (!plantPlacement) continue;
        const plm = plantPool[plantCount++];
        plm.position.set(plantPlacement.x, 0, plantPlacement.z);
        plm.rotation.set(
          0,
          Math.atan2(player.x - plantPlacement.x, player.z - plantPlacement.z),
          0
        );
        plm.visible = true;
      }
    }
    for (let pl = plantCount; pl < plantPool.length; pl++) {
      plantPool[pl].visible = false;
    }

    let fluorescentCount = 0;
    if (fluorescentPool.length > 0) {
      for (let gx = player.gx - WALL_VIEW_RADIUS; gx <= player.gx + WALL_VIEW_RADIUS; gx++) {
        for (let gz = player.gz - WALL_VIEW_RADIUS; gz <= player.gz + WALL_VIEW_RADIUS; gz++) {
          if (fluorescentCount >= fluorescentPool.length) break;
          const flPlacement = getFluorescentPlacement(gx, gz);
          if (!flPlacement) continue;
          const flm = fluorescentPool[fluorescentCount++];
          flm.position.set(flPlacement.x, WALL_HEIGHT - 0.01, flPlacement.z);
          flm.rotation.set(0, flPlacement.yaw, 0);
          flm.visible = true;
        }
      }
      for (let fl = fluorescentCount; fl < fluorescentPool.length; fl++) {
        fluorescentPool[fl].visible = false;
      }
    }

    let activeCount = 0;
    let revealChanged = false;
    for (let i = 0; i < MAX_ENCOUNTER_MEN; i++) {
      const slot = encounterSlots[i];
      if (!slot.alive) {
        labelDummy.scale.set(0, 0, 0);
        labelDummy.updateMatrix();
        instancedLabels.setMatrixAt(i, labelDummy.matrix);
        if (slot.leaving) {
          slot.opacity = Math.max(0, slot.opacity - dt * 1.4);
          slot.mat.opacity = slot.opacity;
          slot.leaveStepTimer -= dt;
          if (slot.leaveStepTimer <= 0 && slot.opacity > 0.1) {
            playRandomFootstep(0.8 * slot.opacity, 1.55);
            slot.leaveStepTimer = 0.17;
          }
          slot.x += slot.leaveVx * dt;
          slot.z += slot.leaveVz * dt;
          const bounceY = Math.abs(Math.sin(elapsed * 19 + i * 1.7)) * 0.16;
          const billboardYaw = Math.atan2(player.x - slot.x, player.z - slot.z);
          slot.mesh.position.set(slot.x, bounceY, slot.z);
          slot.mesh.rotation.set(0, billboardYaw, 0);
          if (slot.opacity <= 0) {
            slot.leaving = false;
            slot.mesh.visible = false;
          }
        }
        continue;
      }

      activeCount++;
      slot.opacity = Math.min(1, slot.opacity + dt * 1.6);
      slot.mat.opacity = slot.opacity;

      if (slot.reveal < 1) {
        slot.reveal = Math.min(1, slot.reveal + dt / 0.34);
        revealArray[i] = slot.reveal;
        revealChanged = true;
      }

      if (slot.laughTimer > 0) {
        slot.laughTimer -= dt;
        if (slot.laughTimer <= 0) {
          slot.laughTimer = 0;
          if (slot.mat.map !== manTexture) {
            slot.mat.map = manTexture;
            slot.mat.needsUpdate = true;
          }
        }
      }

      const rowLerp = 1 - Math.exp(-7 * dt);
      slot.x += (slot.targetX - slot.x) * rowLerp;
      slot.z += (slot.targetZ - slot.z) * rowLerp;
      slot.labelY += (slot.targetLabelY - slot.labelY) * rowLerp;

      const billboardYaw = Math.atan2(player.x - slot.x, player.z - slot.z);
      slot.mesh.position.set(slot.x, 0, slot.z);
      slot.mesh.rotation.set(0, billboardYaw, 0);

      labelDummy.position.set(slot.x, slot.labelY, slot.z);
      labelDummy.quaternion.copy(camera.quaternion);
      labelDummy.scale.set(1, 1, 1);
      labelDummy.updateMatrix();
      instancedLabels.setMatrixAt(i, labelDummy.matrix);
    }
    instancedLabels.instanceMatrix.needsUpdate = true;
    if (revealChanged) {
      revealAttr.needsUpdate = true;
    }

    if (inEncounter && activeCount > 0) {
      addAnxiety(ENCOUNTER_ANXIETY_RATE * dt);
    }

    renderFrame();
  }

  applyPs1Jitter(vendingMat);
  applyPs1Jitter(waterCoolerMat);
  applyPs1Jitter(fluorescentMat);
  applyPs1Jitter(womensSignMat);
  for (const mat of posterMats) {
    applyPs1Jitter(mat);
  }
  scene.traverse((obj) => {
    if (obj.isMesh && obj.material) {
      const mats = Array.isArray(obj.material) ? obj.material : [obj.material];
      for (const mat of mats) {
        if (mat.isMeshStandardMaterial) {
          applyPs1Jitter(mat);
        }
      }
    }
  });

  animate();
}

init();
