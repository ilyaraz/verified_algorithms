/* No runtime dependencies: this atlas works from a static host or file://. */
(() => {
  'use strict';
  const data = window.LEAN_GRAPH;
  const $ = (selector) => document.querySelector(selector);
  const escape = (text) => String(text).replace(/[&<>"']/g, (c) => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
  const byId = new Map(data.nodes.map((n) => [n.id, n]));
  const initial = 'WordRam.run_resume';
  const state = {selected: initial, mode: 'focus', module: '', kind: 'all', query: ''};
  const camera = {x: 0, y: 0, scale: 1};
  let bounds = {width: 900, height: 600};
  let pointer = null;
  let moved = false;
  let shownNodes = [];
  const svg = $('#graph');
  const shortName = (node) => node.id.replace(/^WordRam\./, '').replace(/^Examples\./, '');
  const glyph = (category) => `<i class="${category === 'statement' ? 'thm' : 'def'}-dot" aria-hidden="true"></i>`;

  function readHash() {
    const p = new URLSearchParams(location.hash.slice(1));
    state.selected = byId.has(p.get('decl')) ? p.get('decl') : initial;
    state.mode = p.get('view') === 'all' ? 'all' : 'focus';
    state.module = data.modules.includes(p.get('module')) ? p.get('module') : '';
    state.kind = ['definition', 'statement'].includes(p.get('kind')) ? p.get('kind') : 'all';
  }
  function writeHash() {
    const p = new URLSearchParams({decl: state.selected, view: state.mode});
    if (state.module) p.set('module', state.module);
    if (state.kind !== 'all') p.set('kind', state.kind);
    const hash = `#${p}`;
    if (hash !== location.hash) history.pushState(null, '', hash);
  }
  function matches(n) {
    return (!state.module || n.module === state.module) && (state.kind === 'all' || n.category === state.kind);
  }
  function renderIndex() {
    const previouslyOpen = new Set([...document.querySelectorAll('.module-group[open]')].map((el) => el.dataset.module));
    const query = state.query.trim().toLocaleLowerCase();
    const nodes = data.nodes.filter((n) => matches(n) && (!query || `${n.id} ${n.description} ${n.kind}`.toLocaleLowerCase().includes(query)));
    $('#index-count').textContent = nodes.length;
    $('#declaration-list').innerHTML = nodes.length ? data.modules.map((module) => {
      const members = nodes.filter((n) => n.module === module);
      if (!members.length) return '';
      const open = query || state.module || previouslyOpen.has(module) || members.some((n) => n.id === state.selected);
      return `<details class="module-group" data-module="${module}" ${open ? 'open' : ''}><summary>${module}<span>${members.length}</span></summary>${members.map((n) => `<button class="declaration-item ${n.id === state.selected ? 'selected' : ''}" data-id="${escape(n.id)}" aria-label="${escape(n.id)}" ${n.id === state.selected ? 'aria-current="true"' : ''} title="${escape(n.description)}">${glyph(n.category)}<span class="item-name">${escape(shortName(n))}</span></button>`).join('')}</details>`;
    }).join('') : '<p class="empty-list">No matching declarations.<br>Try a shorter name or clear the filters.</p>';
    document.querySelectorAll('[data-kind]').forEach((button) => button.setAttribute('aria-pressed', button.dataset.kind === state.kind));
  }
  function relationList(ids, direction) {
    if (!ids.length) return `<p class="relation-empty">${direction === 'uses' ? 'No references to other project declarations.' : 'No other authored declaration references this entry.'}</p>`;
    return ids.map((id) => {
      const n = byId.get(id);
      const edge = data.edges.find((e) => direction === 'uses' ? e.source === id && e.target === state.selected : e.source === state.selected && e.target === id);
      const role = edge.roles.map((r) => r === 'type' ? 'type or signature' : 'definition or proof body').join(' and ');
      return `<button class="relation-item" data-id="${escape(id)}" title="Referenced in ${role}">${glyph(n.category)}<span class="relation-name">${escape(shortName(n))}</span><span class="relation-arrow" aria-hidden="true">↗</span></button>`;
    }).join('');
  }
  function renderInspector() {
    const n = byId.get(state.selected);
    $('#inspector').innerHTML = `<div class="inspector-label">Declaration details<span aria-hidden="true">⌘</span></div>
      <span class="badge ${n.category}">${glyph(n.category)}${n.category === 'statement' ? 'Statement' : 'Definition'} · ${escape(n.kind)}</span>${n.private ? '<span class="private-label">private</span>' : ''}
      <h2>${escape(shortName(n))}</h2><p class="qualified-name">${escape(n.id)}</p>
      <p class="description">${escape(n.description)}</p>
      <a class="source-link" href="${escape(n.sourceUrl)}" target="_blank" rel="noopener"><span>${escape(n.file)}:${n.line}</span><span aria-hidden="true">↗</span></a>
      <button class="focus-button" id="focus-selected">Explore this neighborhood</button>
      <details class="code-section" open><summary>Lean declaration</summary><pre><code>${escape(n.source)}</code></pre></details>
      <section class="relation-section"><h3>Uses <span>${n.dependencies.length}</span></h3><p class="relation-key">References in its type, definition, or proof.</p>${relationList(n.dependencies, 'uses')}</section>
      <section class="relation-section"><h3>Used by <span>${n.dependents.length}</span></h3>${relationList(n.dependents, 'users')}</section>`;
    $('#focus-selected').addEventListener('click', () => {
      state.mode = 'focus'; state.module = ''; state.kind = 'all'; state.query = ''; $('#search').value = '';
      update();
    });
  }
  function layout(nodes) {
    const positions = new Map();
    const labels = [];
    const W = 246, H = 58, gap = 80, xGap = 310;
    if (state.mode === 'focus' && nodes.some((n) => n.id === state.selected)) {
      const selected = byId.get(state.selected);
      const deps = nodes.filter((n) => selected.dependencies.includes(n.id));
      const users = nodes.filter((n) => selected.dependents.includes(n.id) && !selected.dependencies.includes(n.id));
      const depCols = Math.max(1, Math.ceil(deps.length / 9));
      const userCols = Math.max(1, Math.ceil(users.length / 9));
      const rows = Math.max(Math.min(9, deps.length), Math.min(9, users.length), 1);
      const centerX = depCols * xGap;
      positions.set(selected.id, {x: centerX, y: 50 + (rows - 1) * gap / 2});
      const place = (list, startX) => list.forEach((n, i) => positions.set(n.id, {x: startX + Math.floor(i / 9) * xGap, y: 50 + (i % 9) * gap}));
      place(deps, 0); place(users, centerX + xGap);
      labels.push({x: 0, text: 'DEPENDS ON'}, {x: centerX, text: 'SELECTED'}, {x: centerX + xGap, text: 'USED BY'});
      bounds = {width: centerX + xGap + (users.length ? (userCols - 1) * xGap + W : W * .4), height: rows * gap + 35};
    } else {
      const modules = data.modules.filter((m) => nodes.some((n) => n.module === m));
      let nextX = 0;
      let maxRows = 1;
      modules.forEach((module) => {
        const members = nodes.filter((n) => n.module === module);
        // Keep a module readable when it is selected on its own.
        const rowsPerColumn = modules.length === 1 ? 9 : 18;
        labels.push({x: nextX, text: module.toUpperCase()});
        members.forEach((n, i) => positions.set(n.id, {x: nextX + Math.floor(i / rowsPerColumn) * xGap, y: 50 + (i % rowsPerColumn) * gap}));
        nextX += Math.ceil(members.length / rowsPerColumn) * xGap + 30;
        maxRows = Math.max(maxRows, Math.min(rowsPerColumn, members.length));
      });
      bounds = {width: Math.max(W, nextX - 30 - xGap + W), height: maxRows * gap + 35};
    }
    return {positions, labels, W, H};
  }
  function renderGraph(fit = true) {
    const selected = byId.get(state.selected);
    const neighborhood = new Set([selected.id, ...selected.dependencies, ...selected.dependents]);
    shownNodes = data.nodes.filter((n) => matches(n) && (state.mode === 'all' || neighborhood.has(n.id)));
    const ids = new Set(shownNodes.map((n) => n.id));
    const edges = data.edges.filter((e) => ids.has(e.source) && ids.has(e.target) && (state.mode === 'all' || e.source === state.selected || e.target === state.selected));
    const {positions, labels, W, H} = layout(shownNodes);
    $('#edges').innerHTML = edges.map((edge) => {
      const from = positions.get(edge.source), to = positions.get(edge.target);
      const active = edge.source === state.selected || edge.target === state.selected;
      const x1 = from.x + W, y1 = from.y + H / 2, x2 = to.x, y2 = to.y + H / 2;
      let path;
      if (from.x < to.x) {
        const distance = Math.max(35, (x2 - x1) * .5);
        path = `M${x1},${y1} C${x1 + distance},${y1} ${x2 - distance},${y2} ${x2},${y2}`;
      } else if (from.x === to.x) {
        path = `M${x1},${y1} C${x1 + 45},${y1} ${x1 + 45},${y2} ${x1},${y2}`;
      } else {
        path = `M${from.x},${y1} C${from.x - 42},${y1} ${to.x + W + 42},${y2} ${to.x + W},${y2}`;
      }
      return `<path class="edge ${active ? 'active' : state.mode === 'all' ? 'muted' : ''}" d="${path}"><title>${escape(edge.source)} → ${escape(edge.target)}</title></path>`;
    }).join('');
    $('#nodes').innerHTML = labels.map((l) => `<text class="column-label" x="${l.x}" y="20">${escape(l.text)}</text>`).join('') + shownNodes.map((n) => {
      const p = positions.get(n.id), name = shortName(n);
      const label = name.length > 31 ? name.slice(0, 29) + '…' : name;
      const icon = n.category === 'statement' ? '<path class="node-icon" d="M17 19 L22 24 L17 29 L12 24 Z"/>' : '<rect class="node-icon" x="13" y="20" width="8" height="8" rx="2"/>';
      return `<g class="graph-node ${n.category} ${n.id === state.selected ? 'selected' : ''}" transform="translate(${p.x},${p.y})" data-id="${escape(n.id)}" role="button" tabindex="0" aria-label="${escape(n.id)}: ${escape(n.description)}" aria-pressed="${n.id === state.selected}"><title>${escape(n.id)}\n${escape(n.description)}</title><rect class="node-box" width="${W}" height="${H}" rx="${n.category === 'statement' ? 3 : 9}"/>${icon}<text class="node-label" x="30" y="28">${escape(label)}</text><text class="node-meta" x="30" y="45">${escape(n.module)} · ${escape(n.kind)}</text></g>`;
    }).join('');
    $('#graph-title').textContent = state.mode === 'focus' ? `${shortName(selected)} · direct neighborhood` : (state.module || 'Entire library') + ' · all dependencies';
    $('#graph-count').textContent = `${shownNodes.length} nodes · ${edges.length} links`;
    $('#empty-graph').hidden = shownNodes.length > 0;
    $('#focus-view').setAttribute('aria-pressed', state.mode === 'focus');
    $('#all-view').setAttribute('aria-pressed', state.mode === 'all');
    $('#module-filter').value = state.module;
    if (fit) fitGraph();
  }
  function applyCamera() {
    $('#viewport').setAttribute('transform', `translate(${camera.x},${camera.y}) scale(${camera.scale})`);
    $('#zoom-level').textContent = `${Math.round(camera.scale * 100)}%`;
  }
  function fitGraph() {
    const {width, height} = svg.getBoundingClientRect();
    camera.scale = Math.min(1.3, Math.max(.03, Math.min((width - 50) / bounds.width, (height - 110) / bounds.height)));
    camera.x = (width - bounds.width * camera.scale) / 2;
    camera.y = (height - bounds.height * camera.scale) / 2 + 2;
    applyCamera();
  }
  function zoom(factor, x, y) {
    const rect = svg.getBoundingClientRect();
    x ??= rect.width / 2; y ??= rect.height / 2;
    const oldScale = camera.scale;
    camera.scale = Math.max(.03, Math.min(3, oldScale * factor));
    camera.x = x - (x - camera.x) * camera.scale / oldScale;
    camera.y = y - (y - camera.y) * camera.scale / oldScale;
    applyCamera();
  }
  function update({fit = true, push = true} = {}) {
    renderIndex(); renderInspector(); renderGraph(fit);
    if (push) writeHash();
  }
  function select(id, fromRelation = false) {
    if (!byId.has(id)) return;
    state.selected = id;
    if (fromRelation) {state.kind = 'all'; state.module = '';}
    update({fit: state.mode === 'focus' || fromRelation});
  }
  document.addEventListener('click', (event) => {
    const item = event.target.closest('[data-id]');
    if (item && !(moved && item.closest('svg'))) select(item.dataset.id, Boolean(item.closest('#inspector')));
  });
  svg.addEventListener('keydown', (event) => {
    const item = event.target.closest('[data-id]');
    if (item && ['Enter', ' '].includes(event.key)) {event.preventDefault(); select(item.dataset.id);}
    if (['+', '='].includes(event.key)) {event.preventDefault(); zoom(1.2);}
    if (event.key === '-') {event.preventDefault(); zoom(1 / 1.2);}
  });
  $('#search').addEventListener('input', (event) => {state.query = event.target.value; renderIndex();});
  document.querySelectorAll('[data-kind]').forEach((button) => button.addEventListener('click', () => {
    state.kind = button.dataset.kind; update();
  }));
  $('#module-filter').innerHTML += data.modules.map((m) => `<option value="${m}">${m}</option>`).join('');
  $('#module-filter').addEventListener('change', (event) => {state.module = event.target.value; state.mode = 'all'; update();});
  $('#focus-view').addEventListener('click', () => {state.mode = 'focus'; update();});
  $('#all-view').addEventListener('click', () => {state.mode = 'all'; update();});
  $('#zoom-in').addEventListener('click', () => zoom(1.25));
  $('#zoom-out').addEventListener('click', () => zoom(.8));
  $('#fit').addEventListener('click', fitGraph);
  $('#reset').addEventListener('click', () => {
    Object.assign(state, {selected: initial, mode: 'focus', module: '', kind: 'all', query: ''});
    $('#search').value = ''; update();
  });
  $('#about-button').addEventListener('click', () => $('#about').showModal());
  document.addEventListener('keydown', (event) => {
    if (event.key === '/' && !event.ctrlKey && !event.metaKey && !['INPUT', 'TEXTAREA', 'SELECT'].includes(document.activeElement.tagName) && !$('#about').open) {
      event.preventDefault(); $('#search').focus();
    }
  });
  svg.addEventListener('wheel', (event) => {
    event.preventDefault();
    const r = svg.getBoundingClientRect();
    zoom(Math.exp(-event.deltaY * .0015), event.clientX - r.left, event.clientY - r.top);
  }, {passive: false});
  svg.addEventListener('pointerdown', (event) => {
    if (event.button !== 0) return;
    pointer = {id: event.pointerId, x: event.clientX, y: event.clientY, cx: camera.x, cy: camera.y}; moved = false;
  });
  svg.addEventListener('pointermove', (event) => {
    if (!pointer || event.pointerId !== pointer.id) return;
    const dx = event.clientX - pointer.x, dy = event.clientY - pointer.y;
    if (Math.hypot(dx, dy) > 4) {moved = true; svg.classList.add('dragging'); svg.setPointerCapture(event.pointerId);}
    if (moved) {camera.x = pointer.cx + dx; camera.y = pointer.cy + dy; applyCamera();}
  });
  function release(event) {
    if (pointer && svg.hasPointerCapture(pointer.id)) svg.releasePointerCapture(pointer.id);
    pointer = null; svg.classList.remove('dragging');
    if (event.type === 'pointercancel') moved = false;
  }
  svg.addEventListener('pointerup', release); svg.addEventListener('pointercancel', release);
  window.addEventListener('pointerup', release);
  window.addEventListener('hashchange', () => {readHash(); update({push: false});});
  new ResizeObserver(() => fitGraph()).observe(svg);
  $('#definition-count').textContent = data.nodes.filter((n) => n.category === 'definition').length;
  $('#statement-count').textContent = data.nodes.filter((n) => n.category === 'statement').length;
  readHash(); update({push: false});
})();
