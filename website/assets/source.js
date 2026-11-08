function revealLine() {
  const match = /^#L\d+$/.test(location.hash);
  if (match) document.getElementById(location.hash.slice(1))?.scrollIntoView({block: 'center'});
}
window.addEventListener('hashchange', revealLine);
window.addEventListener('load', revealLine);
