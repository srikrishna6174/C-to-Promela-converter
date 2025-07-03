
#include <stdio.h>

int main() {
    int x = 5;
    int y = 10;
    
    if (x < y) {
        printf("x is less than y\n");
    }
    
    while (x < y) {
        x++;
        printf("x = %d\n", x);
    }
    
    return 0;
}
