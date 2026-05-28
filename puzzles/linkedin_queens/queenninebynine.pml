/* 9x9 LinkedIn Queens solution 

This code is part of my blog post on solving the LinkedIn-Queens puzzle:  
https://wyounas.github.io/model-checking/puzzles/2025/10/18/exploring-all-solutions-to-linkedin-queens-puzzle-with-a-sat-solver-and-two-model-checkers/
*/

#define N 9
#define ADJ1(a,b) ((a) == (b) + 1 || (b) == (a) + 1)

byte result[N];
bool rows[N];
bool cols[N];
bool regions[N];
byte qcol[N];          

/* Region 1 */
inline ChooseRegion1() {
    if
    :: cell =  1
    :: cell =  2
    :: cell = 10
    :: cell = 19
    :: cell = 28
    :: cell = 37
    :: cell = 46
    fi
}
/* Region 2 (singleton) */
inline ChooseRegion2() { if :: cell = 11 fi }

/* Region 3 */
inline ChooseRegion3() {
    if
    :: cell =  3 :: cell =  4 :: cell =  5 :: cell =  6 :: cell =  7 :: cell =  8 :: cell =  9
    :: cell = 12 :: cell = 17 :: cell = 18 :: cell = 20 :: cell = 21 :: cell = 22 :: cell = 23
    :: cell = 31 :: cell = 40 :: cell = 41 :: cell = 48 :: cell = 49 :: cell = 58 :: cell = 67
    fi
}

/* Region 4 */
inline ChooseRegion4() {
    if
    :: cell = 13 :: cell = 14 :: cell = 15 :: cell = 16
    :: cell = 24 :: cell = 25 :: cell = 26 :: cell = 27
    :: cell = 33 :: cell = 35 :: cell = 36 :: cell = 45
    fi
}

/* Region 5 */
inline ChooseRegion5() {
    if
    :: cell = 29 :: cell = 30 :: cell = 38 :: cell = 39
    :: cell = 47 :: cell = 55 :: cell = 56 :: cell = 64
    fi
}

/* Region 6 (singleton) */
inline ChooseRegion6() { if :: cell = 32 fi }

/* Region 7 */
inline ChooseRegion7() {
    if
    :: cell = 34 :: cell = 42 :: cell = 43 :: cell = 44
    :: cell = 50 :: cell = 51 :: cell = 52 :: cell = 53 :: cell = 54
    :: cell = 59 :: cell = 60 :: cell = 61 :: cell = 62 :: cell = 63
    :: cell = 68 :: cell = 69 :: cell = 71 :: cell = 72
    :: cell = 77 :: cell = 78 :: cell = 80 :: cell = 81
    fi
}

/* Region 8 */
inline ChooseRegion8() {
    if
    :: cell = 57 :: cell = 65 :: cell = 66 :: cell = 73 :: cell = 74 :: cell = 75 :: cell = 76
    fi
}

/* Region 9 */
inline ChooseRegion9() { if :: cell = 70 :: cell = 79 fi }

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
        :: region == 5 -> ChooseRegion5()
        :: region == 6 -> ChooseRegion6()
        :: region == 7 -> ChooseRegion7()
        :: region == 8 -> ChooseRegion8()
        :: region == 9 -> ChooseRegion9()
        fi

        CellToRowCol(cell, row, col);

        // check for row, col, and region constraints
        !rows[row];            
        !cols[col];           
        !regions[region-1];    


        // check for diagonal constraint
        !(
           (row > 0   && rows[row-1] && ADJ1(qcol[row-1], col)) ||
           (row+1 < N && rows[row+1] && ADJ1(qcol[row+1], col))
         );

        // commit the result
        rows[row] = true;
        cols[col] = true;
        regions[region-1] = true;
        qcol[row] = col;       
        result[region-1] = cell;

        
    }

    _ = result[0];
    assert(false);
}
