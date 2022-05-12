# LFS-FinalProject

Demo Video: https://youtu.be/rcnRg1SbCAw 

This model of Conway’s game of life uses a single Board sig, which has a variable field called mappings. The mappings variable keeps track of which cells are ‘alive’ using a set of 2 ints, which refer to the x and y coordinates of the cell. If a mapping exists, the cell in that position is considered alive. Otherwise, the cell is dead.

The original game of life is designed to be played with an infinitely-sized board, allowing for turing-completeness and for very large creations. Our model can, of course, only handle finite-sized boards. This leads to the issue of integer overflow at the edges. As a result, we enforce that the edges of the board must be empty. Additionally, while we can simulate the game of life starting from a given state very well even with large bit widths, generating instances having a specific type of structure is very time-consuming in forge, and is therefore impractical with bit widths of more than 4, or with sequences more than 3 states long.

We make the assumption that when looking for a specific structure (e.g. an oscillator, flying machine, etc.), this structure will be small enough to be contained within the center area of the board, and will therefore be unaffected by the enforced board limits (for example, if we are running with a bit width of 4, we assume that everything will fit into an 15x15 bounding box).

Our target goal was to find an oscillator, preferably with a long period. We did achieve this goal, but performance issues meant that we were only able to find shorter oscillators, with periods of 2 or 3 (we able to generate instances having longer periods (such as the Mold Oscillator with period 4), however this involved us having to specify the starting state of the pattern). Our stretch goal was to find a more complicated pattern such as a glider (oscillator that continuously moves in a particular direction). However, due to performance limitations with the size of the board, we were unable to generate a board big enough to generate a glider, and had a hard time detecting movement (or the creation of cells) in a cyclic electrum-style language, because movement or cell creation would imply that the result is no longer a ‘lasso’.

The visualizer for this project shows the board (sized dynamically based off of the number of ints), with live cells represented by black squares, and dead cells represented by blank (white) squares. Scrolling down will take you through all states in the visualization.

