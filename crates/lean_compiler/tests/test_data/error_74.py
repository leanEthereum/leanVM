# Error: multidimensional indexing is only supported on compile-time const
# arrays. `arr = Array(N)` is a runtime allocation, so `arr[0][1]` must be
# rejected
def main():
    arr = Array(4)
    x = arr[0][1] + 1
    return
