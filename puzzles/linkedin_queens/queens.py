"""
Python code to solve Linked-in queens puzzle. 

Please see readme.md for installing PyEDA.

This code is part of my blog post on solving the LinkedIn-Queens puzzle:  
https://wyounas.github.io/model-checking/puzzles/2025/10/18/exploring-all-solutions-to-linkedin-queens-puzzle-with-a-sat-solver-and-two-model-checkers/

"""
from pyeda.inter import *

def solve_linkedin_queens(n, regions_config):
    
    X = exprvars('x', n, n)
    
    constraints = []
    
    print(f"\nBuilding row constraints for {n}x{n} board...")
    for r in range(n):
        row_vars = [X[r,c] for c in range(n)]
        constraints.append(OneHot(*row_vars))
    
    print("\nBuilding column constraints...")
    for c in range(n):
        col_vars = [X[r,c] for r in range(n)]
        constraints.append(OneHot(*col_vars))
    
    print("\nBuilding region constraints...")
    for _, cells in regions_config.items():
        region_vars = [X[r,c] for r, c in cells]
        constraints.append(OneHot(*region_vars))
    
    print("\nBuilding diagonal adjacency constraints...")
    for r in range(n-1):  # Stop before last row
        for c in range(n):
            # Below-left diagonal
            if c > 0:
                constraints.append(~(X[r,c] & X[r+1, c-1]))
            
            # Below-right diagonal
            if c < n-1:
                constraints.append(~(X[r,c] & X[r+1, c+1]))

    S = And(*constraints)
    
    print("Searching for solutions...")
    solutions = list(S.satisfy_all())
    print(f"Found {len(solutions)} solution(s)")
    
    return X, solutions


def display_solution(X, solution, n, regions_config=None):
    print()
    for r in range(n):
        row_str = ""
        for c in range(n):
            if solution[X[r, c]]:
                row_str += " Q "
            else:
                row_str += " . "
        print(row_str)
    
    queen_cells = []
    for r in range(n):
        for c in range(n):
            if solution[X[r, c]]:
                cell_num = r * n + c + 1  
                queen_cells.append(cell_num)

    print(f"Queens at cells: {queen_cells}")
    
    # If regions provided, show region assignment
    if regions_config:
        print("\nRegion layout:")
        region_board = [[0 for _ in range(n)] for _ in range(n)]
        for region_id, cells in regions_config.items():
            for r, c in cells:
                region_board[r][c] = region_id
        
        for row in region_board:
            print(" ".join(f"{r}" for r in row))




def main():
    
    regions = {
        1: [(0, 0), (0, 1), (0, 2), (0, 3)],  # Region 1: cells 1-4 (row 0)
        2: [(1, 0), (1, 1), (1, 2), (1, 3)],  # Region 2: cells 5-8 (row 1)
        3: [(2, 0), (2, 1), (2, 2), (2, 3)],  # Region 3: cells 9-12 (row 2)
        4: [(3, 0), (3, 1), (3, 2), (3, 3)]   # Region 4: cells 13-16 (row 3)
    }
   
    
    X, solutions = solve_linkedin_queens(4, regions)
    
    if solutions:
        print(f"\n\nFound {len(solutions)} solution(s):")
        for i, solution in enumerate(solutions):
            print(f"\n{'='*30}")
            print(f"Solution {i+1}:")
            display_solution(X, solution, 4, regions)
    else:
        print("\nNo solutions found!")
    

if __name__ == "__main__":
    main()