#include <stdio.h>

int main() {
    int n=5;
    int x=0,y=1,z;
    for(int i=0;i<n;i++){
        if(x>0){
            x++;
        }
        else{
            x--;
        }
        if(y<0){
            y--;
        }
        else{
            y++;
        }
    }
    printf("Hello World, I'm dooing loop fission!\n");
    return 0;
}