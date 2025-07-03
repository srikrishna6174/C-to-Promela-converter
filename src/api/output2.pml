
/* Automatically translated from C to Promela */
/* Original file: input.c */

atomic {
    if
        :: (x < y) ->
        printf("x is less than y\n");
    fi;
}
do
    :: (x < y) ->
    atomic {
        x++;
        printf("x = %d\n", x);
    }
    :: else -> break;
od;
