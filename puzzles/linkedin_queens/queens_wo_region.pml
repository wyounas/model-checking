/*

Promela model to solve the 8x8 Linkedin-queens puzzle with following rules:

1. At most one queen in a column.
2. At most one queen in a row.
3. No two queens in adjacent diagonals. 

This one doesn't take into account the 'regions' constraint.

If you run this with `./pan -E -c0 -e` command you'll get 5242 trail files in your directory, each 
containing puzzle's solution.

This code is part of my blog post on solving the LinkedIn-Queens puzzle:  
https://wyounas.github.io/model-checking/puzzles/2025/10/18/exploring-all-solutions-to-linkedin-queens-puzzle-with-a-sat-solver-and-two-model-checkers/

*/

#define N 8
byte   result[N];           
bool   a[N];  

/*

'diags' array below contains row and col coordinates of upper-right (ur) 
and lower-right (lr) adjacent diagonals of a cell in the form,
[ur_row, ur_col, lr_row, lr_col]
*/
byte diags[4]              

inline Choose() {
    if
    :: row = 1;
    :: row = 2;
    :: row = 3;
    :: row = 4;
    :: row = 5;
    :: row = 6;
    :: row = 7;
    :: row = 8;
    fi;
}

inline Write() {
    int ii;
    for (ii : 1 .. N) {
        printf("%d, ", result[ii-1]);
    }
    printf("\n");
}

active proctype Queens() {
    byte col = 1, row, k;
    byte p_ud, p_ld, ud, ld;
    byte ur_row, ur_col, lr_row, lr_col;

    byte curr_row;
    byte curr_col;
    // default values
    diags[0] = 100;
    diags[1] = 100; 
    diags[2] = 100;
    diags[3] = 100;

    /*
    We process columns in sequence one by one. If the current cell is an adjacent diagonal
    of a queen we've placed in, we block. Also, if we've already placed a queen in the row
    that we're going to process, we block. Otherwise, we continue, mark the position of 
    the queen in the row and store the row in the 'result'. Before ending the iteration, we
    note the adjacent diagonals of cell being processed, to be used in the next iteration.
    */
    do
    :: Choose();
        !a[row-1];                   
        
        ur_row = diags[0];
        ur_col = diags[1]
        lr_row = diags[2]
        lr_col = diags[3]


        curr_row = row - 1;
        curr_col = col - 1;

        if 
        :: curr_row == ur_row && ur_col == curr_col ||  curr_row == lr_row && lr_col == curr_col ->
            !true;
        :: else -> skip 
        fi
        
        
        a[row-1]    = true;
        result[col-1] = row;

        printf("Row %d, col %d, k %d, N %d \n", row, col, k, N)

        // storing upper-right adjacent diagnol's row and col
        diags[0] = curr_row - 1;
        diags[1] = curr_col + 1;
        // storing lower-right adjacent diagnol's row and col
        diags[2] = curr_row + 1;
        diags[3] = curr_col + 1;

        printf("diag-0 %d, diag-1 %d, diag-2 %d, diag-3 %d \n", diags[0], diags[1], diags[2], diags[3])
        if 
        :: col == N ->
            break 
        :: else ->
            col++
        fi ;
    od;

    _ = result[0];
    Write();
    assert(false);
}