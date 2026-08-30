#include <stdio.h>


int main() {
    int x = 0;
    int n = 2;

    for (int i = 0; i < n; i++) {
        if (i <= 4) {
            x += 100;
        } else {
            x += 2;
        }
    }

    printf("%d\n", x);

    return 0;
}
