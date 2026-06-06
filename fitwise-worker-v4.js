// fitwise-worker-v4.js - 装多多 FIT WISE Web Worker (v4 - Height Toggle)
// 完整装箱管线：排序 → 多容器打包（含自动升级箱型）→ 返回结果
// 由主线程并行调用，每个 Worker 处理一个策略

const EPS = 0.5, LOCAL_RADIUS = 250;
let useInternalHeight = false;
function getContainerEffH(c) { return useInternalHeight && c.H && c.id !== 'custom' ? c.H : (c.doorH || c.H); }

// ── 旋转配置 ──────────────────────────────────
function getRotations(origL, origW, origH, orient) {
  if (orient === 'fixed') return [[origL, origW, origH]];
  if (orient === 'honly') {
    const rots = [[origL, origW, origH], [origW, origL, origH]];
    const seen = new Set(); const unique = [];
    for (const r of rots) { const k = r.join(','); if (!seen.has(k)) { seen.add(k); unique.push(r); } }
    return unique;
  }
  const all = [[origL, origW, origH], [origL, origH, origW], [origW, origL, origH], [origW, origH, origL], [origH, origL, origW], [origH, origW, origL]];
  const seen = new Set(); const unique = [];
  for (const r of all) { const k = r.join(','); if (!seen.has(k)) { seen.add(k); unique.push(r); } }
  return unique.sort((a, b) => a[2] - b[2]);
}

// ── 几何工具 ──────────────────────────────────
function getBoxCenter(b) {
  return { cx: b.px + b.pl / 2, cy: b.py + b.ph / 2, cz: b.pz + b.pw / 2 };
}

function deduplicatePoints(pts, EPS_MERGE) {
  if (!EPS_MERGE) EPS_MERGE = 15;
  if (pts.length === 0) return pts;
  const sorted = [...pts].sort((a, b) => {
    const dx = a.x - b.x; if (Math.abs(dx) > 1) return dx;
    const dz = a.z - b.z; if (Math.abs(dz) > 1) return dz;
    return a.y - b.y;
  });
  const result = [];
  for (const p of sorted) {
    let isDupe = false;
    for (const r of result) {
      if (Math.abs(p.x-r.x) < EPS_MERGE && Math.abs(p.y-r.y) < EPS_MERGE && Math.abs(p.z-r.z) < EPS_MERGE) {
        isDupe = true; if (p.y < r.y) { r.x=p.x; r.y=p.y; r.z=p.z; } break;
      }
    }
    if (!isDupe) result.push({x:p.x, y:p.y, z:p.z});
  }
  return result;
}

// ── 排序策略（与主文件相同）───────────────────
function compositeScore(box) {
  const vol = box.origL * box.origW * box.origH;
  const baseArea = box.origL * box.origW;
  const density = (box.unitWeight || 0) * 1e6 / (vol || 1);
  return vol * 1.0 + (baseArea / 1000) * 5 + density * 10;
}
function layerScore(box) {
  const vol = box.origL * box.origW * box.origH;
  return -box.origH * 1000000 + vol;
}
function widthHeightScore(box) { return box.origW * box.origH; }

function getSortFunction(strategyId) {
  switch (strategyId) {
    case 'vol_desc':     return (a, b) => (b.origL * b.origW * b.origH) - (a.origL * a.origW * a.origH);
    case 'height_desc':  return (a, b) => b.origH - a.origH;
    case 'weight_desc':  return (a, b) => (b.unitWeight || 0) - (a.unitWeight || 0);
    case 'composite':    return (a, b) => compositeScore(b) - compositeScore(a);
    case 'layer_first':  return (a, b) => layerScore(a) - layerScore(b);
    case 'width_height': return (a, b) => widthHeightScore(b) - widthHeightScore(a);
    case 'heavy_bottom': return (a, b) => {
      const TH = 25;
      const aH = (a.unitWeight || 0) >= TH ? 0 : 1;
      const bH = (b.unitWeight || 0) >= TH ? 0 : 1;
      if (aH !== bH) return aH - bH;
      return (b.unitWeight || 0) - (a.unitWeight || 0);
    };
    default: return (a, b) => 0;
  }
}

// ── 核心：extremePointPacking（批量分组优化版 v2）─
function extremePointPacking(boxes, cL, cW, cH, maxWeight) {
  // 0. 规范化尺寸
  boxes.forEach(b => { b.origL = parseFloat(b.origL) || 0; b.origW = parseFloat(b.origW) || 0; b.origH = parseFloat(b.origH) || 0; });
  
  // 1. 合并相同箱子为 Group（关键优化：2355件→4-5组）
  const groupMap = new Map();
  for (const box of boxes) {
    const key = `${box.origL}|${box.origW}|${box.origH}|${box.orient}|${box.unitWeight || 0}`;
    if (!groupMap.has(key)) {
      groupMap.set(key, { template: {...box}, count: 0 });
    }
    groupMap.get(key).count++;
  }
  const groups = Array.from(groupMap.values());

  // 2. 初始化
  let extremePoints = [{x:0, y:0, z:0}];
  let packed = [], unpacked = [], totalWeight = 0;
  const EPS = 0.5;
  const CELL = 100;
  const GX = Math.max(1, Math.ceil(cL/CELL)), GY = Math.max(1, Math.ceil(cH/CELL)), GZ = Math.max(1, Math.ceil(cW/CELL));
  const grid = Array.from({length:GX},()=>Array.from({length:GY},()=>Array.from({length:GZ},()=>[])));
  function gridAdd(idx) {
    const b = packed[idx];
    const x0=Math.max(0,Math.floor(b.px/CELL)), x1=Math.min(GX-1,Math.floor((b.px+b.pl)/CELL));
    const y0=Math.max(0,Math.floor(b.py/CELL)), y1=Math.min(GY-1,Math.floor((b.py+b.ph)/CELL));
    const z0=Math.max(0,Math.floor(b.pz/CELL)), z1=Math.min(GZ-1,Math.floor((b.pz+b.pw)/CELL));
    for(let x=x0;x<=x1;x++) for(let y=y0;y<=y1;y++) for(let z=z0;z<=z1;z++) grid[x][y][z].push(idx);
  }
  function gridNeighbors(ex,ey,ez) {
    const gx=Math.max(0,Math.min(GX-1,Math.floor(ex/CELL)));
    const gy=Math.max(0,Math.min(GY-1,Math.floor(ey/CELL)));
    const gz=Math.max(0,Math.min(GZ-1,Math.floor(ez/CELL)));
    const s=new Set();
    for(let dx=-1;dx<=1;dx++) for(let dy=-1;dy<=1;dy++) for(let dz=-1;dz<=1;dz++){
      const nx=gx+dx,ny=gy+dy,nz=gz+dz;
      if(nx>=0&&nx<GX&&ny>=0&&ny<GY&&nz>=0&&nz<GZ) for(const i of grid[nx][ny][nz]) s.add(i);
    }
    return s;
  }
  function isInsideAnyBox(px, py, pz) {
    for (const b of packed) {
      if (px > b.px+EPS && px < b.px+b.pl-EPS && py > b.py+EPS && py < b.py+b.ph-EPS && pz > b.pz+EPS && pz < b.pz+b.pw-EPS) return true;
    }
    return false;
  }
  function hasOverlapGrid(x, z, y, l, w, h) {
    const OLAP_EPS = 0.1;
    for (const idx of gridNeighbors(x+l/2, y+h/2, z+w/2)) {
      const b = packed[idx];
      if (x < b.px+b.pl-OLAP_EPS && x+l > b.px+OLAP_EPS && z < b.pz+b.pw-OLAP_EPS && z+w > b.pz+OLAP_EPS && y < b.py+b.ph-OLAP_EPS && y+h > b.py+OLAP_EPS) return true;
    }
    return false;
  }

  // 3. 处理每个Group（批量放置）
  let totalPlaced = 0;
  for (const group of groups) {
    const template = group.template;
    const rotations = getRotations(template.origL, template.origW, template.origH, template.orient);
    let remaining = group.count;

    while (remaining > 0) {
      // 极端点评分排序
      const scoredEPs = extremePoints.map(ep => {
        let posScore = (cL - ep.x) * 10000 + (cW - ep.z) * 100 + (cH - ep.y);
        let fitBonus = 0;
        for (const b of packed) {
          if (Math.abs(ep.x - (b.px + b.pl)) < 2) fitBonus += 100;
          if (Math.abs(ep.z - (b.pz + b.pw)) < 2) fitBonus += 100;
          if (ep.y < 1) fitBonus += 50;
        }
        return { ep, score: posScore + fitBonus };
      });
      const sortedEPs = scoredEPs.sort((a,b)=>b.score-a.score).map(item=>item.ep);
      let placedInThisRound = false;

      for (const ep of sortedEPs) {
        if (placedInThisRound) break;
        if (isInsideAnyBox(ep.x, ep.y, ep.z)) continue;

        // 计算支撑高度
        let baseY = ep.y;
        for (const b of packed) {
          if (ep.x > b.px-EPS && ep.x < b.px+b.pl+EPS && ep.z > b.pz-EPS && ep.z < b.pz+b.pw+EPS && Math.abs(ep.y-(b.py+b.ph)) < EPS) {
            baseY = Math.max(baseY, b.py + b.ph);
          }
        }

        for (const rot of rotations) {
          const [l, w, h] = rot;
          if (ep.x + l > cL + EPS || baseY + h > cH + EPS || ep.z + w > cW + EPS) continue;
          if (hasOverlapGrid(ep.x, ep.z, baseY, l, w, h)) continue;

          const unitWeight = template.unitWeight || 0;
          const maxCountX = Math.min(remaining, Math.floor((cL - ep.x) / l));
          if (maxCountX <= 0) continue;
          
          let actualCount = 0;
          for (let k = 0; k < maxCountX; k++) {
            const xOff = ep.x + k * l;
            if (hasOverlapGrid(xOff, ep.z, baseY, l, w, h)) break;
            if (totalWeight + (actualCount + 1) * unitWeight > maxWeight) break;
            actualCount++;
          }
          if (actualCount <= 0) continue;

          for (let k = 0; k < actualCount; k++) {
            const placedBox = {...template, pl: l, pw: w, ph: h, px: ep.x + k * l, py: baseY, pz: ep.z, unitWeight: unitWeight};
            delete placedBox.count;
            packed.push(placedBox);
            gridAdd(packed.length - 1);
            totalWeight += unitWeight;
          }
          remaining -= actualCount;
          totalPlaced += actualCount;
          placedInThisRound = true;

          if (totalPlaced % 100 === 0 || totalPlaced >= boxes.length) {
            self.postMessage({ type: 'progress', packedCount: totalPlaced, totalCount: boxes.length });
          }

          // 先过滤再添加（避免误删新边界EP）
          const rMinX = ep.x, rMaxX = ep.x + actualCount * l;
          const rMinY = baseY, rMaxY = baseY + h;
          const rMinZ = ep.z, rMaxZ = ep.z + w;
          extremePoints = extremePoints.filter(ep2 => !(
            ep2.x > rMinX - EPS && ep2.x < rMaxX + EPS &&
            ep2.y > rMinY - EPS && ep2.y < rMaxY + EPS &&
            ep2.z > rMinZ - EPS && ep2.z < rMaxZ + EPS
          ));
          const newEPs = [
            {x: rMaxX, y: rMinY, z: rMinZ},
            {x: rMinX, y: rMaxY, z: rMinZ},
            {x: rMinX, y: rMinY, z: rMaxZ},
            {x: rMaxX, y: rMaxY, z: rMinZ},
            {x: rMaxX, y: rMinY, z: rMaxZ},
            {x: rMinX, y: rMaxY, z: rMaxZ},
            {x: rMaxX, y: rMaxY, z: rMaxZ}
          ];
          for (const nep of newEPs) {
            if (nep.x < cL + EPS && nep.y < cH + EPS && nep.z < cW + EPS && nep.x > -EPS && nep.y > -EPS && nep.z > -EPS) {
              if (!isInsideAnyBox(nep.x, nep.y, nep.z)) extremePoints.push(nep);
            }
          }
          extremePoints = deduplicatePoints(extremePoints, 15);
          break;
        }
      }
      if (!placedInThisRound) break;
    }

    if (remaining > 0) {
      for (let i = 0; i < remaining; i++) {
        unpacked.push({...template, pl: template.origL, pw: template.origW, ph: template.origH});
      }
    }
  }

  // 最终进度
  self.postMessage({ type: 'progress', packedCount: boxes.length, totalCount: boxes.length });
  return { packed, unpacked };
}
// ── 多容器打包（含自动升级箱型）─────────────────
function runMultiContainerPacking(sortedBoxes, container, maxWeight, containersList) {
  let cL = container.L, cW = container.W, cH = getContainerEffH(container);
  let currentMaxWeight = maxWeight;
  const results = [];
  let remaining = [...sortedBoxes];
  let idx = 0;
  const MAX_CONTAINERS = 50;

  function getContainerInfo() {
    const found = containersList.find(c => c.L === cL && c.W === cW && getContainerEffH(c) === cH);
    return found || { name: '自定义', short: '自定义', shortEn: 'Custom', id: 'custom' };
  }

  function tryUpgradeContainer() {
    if (remaining.length === 0) return false;
    const maxItemL = Math.max(...remaining.map(b => b.origL || 0));
    const maxItemW = Math.max(...remaining.map(b => b.origW || 0));
    const maxItemH = Math.max(...remaining.map(b => b.origH || 0));
    const maxItemWt = Math.max(...remaining.map(b => b.unitWeight || 0));
    const suitable = containersList.filter(c => c.id !== 'custom' &&
      c.L >= cL && c.W >= cW && getContainerEffH(c) >= cH &&
      c.maxWeight >= currentMaxWeight &&
      c.L >= maxItemL && c.W >= maxItemW && getContainerEffH(c) >= maxItemH &&
      c.maxWeight >= maxItemWt);
    if (suitable.length > 0) {
      suitable.sort((a, b) => (a.L * a.W * getContainerEffH(a)) - (b.L * b.W * getContainerEffH(b)));
      const upgraded = suitable[0];
      if (upgraded.L > cL || upgraded.W > cW || getContainerEffH(upgraded) > cH || upgraded.maxWeight > currentMaxWeight) {
        cL = upgraded.L; cW = upgraded.W; cH = getContainerEffH(upgraded); currentMaxWeight = upgraded.maxWeight;
        return true;
      }
    }
    return false;
  }

  while (remaining.length > 0 && idx < MAX_CONTAINERS) {
    if (idx > 0) tryUpgradeContainer();

    const overweightItems = remaining.filter(b => (b.unitWeight || 0) > currentMaxWeight);
    if (overweightItems.length > 0) {
      const normalItems = remaining.filter(b => (b.unitWeight || 0) <= currentMaxWeight);
      if (normalItems.length === 0) {
        const containerInfo = getContainerInfo();
        results.push({ containerNum: idx + 1, containerName: containerInfo.name + ' [超重单品无法装载]', containerShort: containerInfo.short, containerShortEn: containerInfo.shortEn, containerId: containerInfo.id, packed: [], unpacked: remaining, usedVol: 0, utilRate: 0, totalWeight: 0, isOverWeight: true });
        break;
      }
      remaining = normalItems;
    }

    const currentContainerVol = cL * cW * cH;
    const res = extremePointPacking(remaining, cL, cW, cH, currentMaxWeight);
    const usedVol = res.packed.reduce((s, b) => s + (b.pl || 0) * (b.pw || 0) * (b.ph || 0), 0);
    const totalWeight = res.packed.reduce((s, b) => s + (b.unitWeight || 0), 0);
    const isOverWeight = totalWeight > currentMaxWeight;
    const containerInfo = getContainerInfo();

    if (res.packed.length > 0) {
      results.push({
        containerNum: idx + 1,
        containerName: containerInfo.name,
        containerShort: containerInfo.short,
        containerShortEn: containerInfo.shortEn,
        containerId: containerInfo.id,
        packed: res.packed,
        unpacked: res.unpacked,
        usedVol: usedVol,
        utilRate: (currentContainerVol > 0 ? +((usedVol / currentContainerVol) * 100).toFixed(1) : 0),
        totalWeight: totalWeight,
        isOverWeight: isOverWeight
      });
    }
    remaining = res.unpacked;
    if (res.packed.length === 0 && remaining.length > 0) break;
    idx++;
  }
  return results;
}

// ── 策略结果评估 ──────────────────────────────
function evaluateStrategyResults(results, containerVol) {
  const totalPacked = results.reduce((s, r) => s + r.packed.length, 0);
  const totalVol = results.reduce((s, r) => s + r.usedVol, 0);
  const containerCount = results.length;
  const avgUtil = (totalVol / (containerCount * containerVol) * 100).toFixed(1);
  let groundBoxes = 0, totalBoxes = 0;
  results.forEach(r => {
    r.packed.forEach(b => { totalBoxes++; if (b.py < 1) groundBoxes++; });
  });
  const stabilityScore = totalBoxes > 0 ? (groundBoxes / totalBoxes * 100).toFixed(1) : 0;
  return { totalPacked, totalVol, containerCount, avgUtil, stabilityScore, score: 0 };
}

// ── Worker 消息处理 ────────────────────────────
self.onmessage = function (e) {
  const { strategyId, strategyName, boxes, container, maxWeight, containersList, useInternalHeight: useInternal } = e.data;
  if (useInternal !== undefined) useInternalHeight = useInternal;
  try {
    const sortFn = getSortFunction(strategyId);
    const sorted = [...boxes].sort(sortFn);
    const t0 = performance.now();
    const results = runMultiContainerPacking(sorted, container, maxWeight, containersList);
    const t1 = performance.now();
    const containerVol = container.L * container.W * getContainerEffH(container);
    const evalInfo = evaluateStrategyResults(results, containerVol);

    self.postMessage({
      type: 'done',
      strategyId,
      strategyName,
      results,
      ...evalInfo,
      timeMs: Math.round(t1 - t0)
    });
  } catch (err) {
    self.postMessage({
      type: 'error',
      strategyId,
      strategyName,
      error: err.message || String(err)
    });
  }
};
