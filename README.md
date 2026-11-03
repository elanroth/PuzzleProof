Saw a puzzle by Gotham Chess where the claim was "White will win, except if black does these exact 11 moves." So, naturally, I wanted to prove it! This repo uses Lean to prove that there is no 10 move solution and that 11 move solution works.

This was vibe proved, and so I've been building a system to evaluate the accuracy of its truth. Meaning, Claude translated this puzzle into Lean, so I need to make sure definitions and theorems characterize the puzzle correctly. I am currently using my own human eyes to evaluate how board positions, piece moving logic, and every other aspect of chess are formalized.

Thanks, [Gotham](https://x.com/GothamChess), for the puzzle!

**[Step through the puzzle and its proof](https://elanroth.github.io/PuzzleProof/viewer/gotham.html)**

## Build

With [elan](https://github.com/leanprover/elan) installed (it fetches the pinned Lean version):

```sh
lake build                 # the chess library: seconds
lake build ChessDemo       # the 11 move solution works: about 3 min
lake build ChessDemoBound  # no 10 move solution: about 45 min on 10 cores
```
