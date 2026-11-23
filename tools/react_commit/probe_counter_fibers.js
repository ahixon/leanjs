// The counter app's committed fiber tree after one click, to check the commit specs' premises against a real run
// (zippy docs/react-proofs.md). Run in a page of the built app (leanjs-logic .lake/scratch/counter/dist) with Zippy's
// MCP `zippy_eval` (no top-level await there). Reads from the FiberRoot's `current`: a DOM node's `__reactFiber$` key
// may point at the old tree.
const b = document.querySelector('button');
b.click();
return new Promise(res => setTimeout(() => {
  const key = Object.keys(b).find(k => k.startsWith('__reactFiber$'));
  let x = b[key]; while (x.return) x = x.return;
  const FR = x.stateNode, R = FR.current, K = R.child, B = K.child;
  const info = f => f && ({tag: f.tag, flags: f.flags, subtreeFlags: f.subtreeFlags, lanes: f.lanes,
    childLanes: f.childLanes, child: !!f.child, sibling: !!f.sibling, deletions: f.deletions});
  res({text: b.textContent, root: info(R), counter: info(K), button: info(B),
    fiberRoot: {pendingLanes: FR.pendingLanes, pooledCache: FR.pooledCache, callbackNode: FR.callbackNode,
      cancelPendingCommit: FR.cancelPendingCommit, timeoutHandle: FR.timeoutHandle,
      hiddenUpdates1: FR.hiddenUpdates[1]}});
}, 50));
