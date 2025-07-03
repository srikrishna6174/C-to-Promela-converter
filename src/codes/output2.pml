

proctype gcd(chan in_gcd;int x;int y) {
    chan ret_gcd = [0] of { int };
    int tmp;
    
    if
        :: ((y == 0)) ->
            in_gcd!x;
            goto end;
        :: else ->
            run gcd(ret_gcd,y,(x % y));
            ret_gcd ? tmp;
            in_gcd!tmp;
            goto end;
    fi;
    
end:
    printf("End of gcd\n");
}
