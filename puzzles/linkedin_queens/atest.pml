active proctype P() {
    byte x = 0;

    if
    :: x = 1      
    :: x = 2     
    :: x = 3  
    :: x = 4
    :: x = 5  
    fi;

    ! (x == 2)
    assert(x == 1);

    printf("Value of x = %d\n", x);
}
