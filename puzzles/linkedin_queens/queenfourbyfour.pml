/*  4x4 LinkedIn Queens (order-independent diagonal check) 

This code is part of my blog post on solving the LinkedIn-Queens puzzle:  
https://wyounas.github.io/model-checking/puzzles/2025/10/18/exploring-all-solutions-to-linkedin-queens-puzzle-with-a-sat-solver-and-two-model-checkers/
*/

#define N 4
#define ADJ1(a,b) ((a) == (b) + 1 || (b) == (a) + 1)

byte result[N];          
bool rows[N];          
bool cols[N];            
bool regions[N];         
byte qcol[N];           

inline ChooseRegion1() { if :: cell = 1 :: cell = 2 :: cell = 3 :: cell = 4 fi }
inline ChooseRegion2() { if :: cell = 5 :: cell = 6 :: cell = 7 :: cell = 8 fi }
inline ChooseRegion3() { if :: cell = 9 :: cell = 10 :: cell = 11 :: cell = 12 fi }
inline ChooseRegion4() { if :: cell = 13 :: cell = 14 :: cell = 15 :: cell = 16 fi }

inline CellToRowCol(cell, row, col) {
    row = ((cell - 1) / N);
    col = ((cell - 1) % N);
}

active proctype Queens() {
    byte region;
    byte cell;
    byte row, col;

    for (region : 1 .. N) {
        if
        :: region == 1 -> ChooseRegion1()
        :: region == 2 -> ChooseRegion2()
        :: region == 3 -> ChooseRegion3()
        :: region == 4 -> ChooseRegion4()
        fi

        CellToRowCol(cell, row, col);

        /* Basic guards */
        !rows[row];            
        !cols[col];             
        !regions[region-1];     


        /* Check immediate diagonals relative to rows that already have queens */
        !(
           (row > 0   && rows[row-1] && ADJ1(qcol[row-1], col)) ||
           (row+1 < N && rows[row+1] && ADJ1(qcol[row+1], col))
         );

        /* Commit placement */
        rows[row] = true;
        cols[col] = true;
        regions[region-1] = true;
        qcol[row] = col;              
        result[region-1] = cell;

    }

    _ = result[0];
    assert(false);   
}
