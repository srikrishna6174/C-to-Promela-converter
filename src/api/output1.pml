
/* Automatically translated from C to Promela */
/* Original file: input.c */

if
    :: (x < y) ->
    printf("x is less than y\n");
fi;
do
    :: (x < y) ->
    x++;
    printf("x = %d\n", x);
    :: else -> break;
od;
