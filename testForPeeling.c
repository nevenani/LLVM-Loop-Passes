#include <stdio.h>

int loop_peeling_example(int x, int n) {
    for (int i = 0; i < n; i++) {
        if (i <= 3) {
            x += 100;
        } else {
            x += 2;
        }
    }
    return x;
}


int main() {
    int n = 10;

    int x = 0;


    printf("%d\n", loop_peeling_example(x, n));

    return 0;
}
