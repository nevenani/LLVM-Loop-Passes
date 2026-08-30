#include<stdio.h>

int main(){
    
    int n = 10;
    int x = 0;
    for(int i = 0; i < n; i++)
        x = i;

    int y = 0;
    for(int i = 0; i < n; i++)
        y += x;

    return 0;

}
