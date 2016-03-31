#include <assert.h>

int has_sequential(int arr[], int size, int key)
{
    assert(size > 0);
    int index = 0;
    while(index < size){
        if arr[index] == key{
            return index;
        }
    }
    return size;
}


int has_binary(int arr[], int size, int key)
{
    //TODO
    return size;
}
