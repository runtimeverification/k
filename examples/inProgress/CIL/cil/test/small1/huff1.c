unsigned short read2Target(unsigned char * ptr )
{
    if (1 /* targetNotLikeHost */) {
        return ((unsigned short )(((int )(*ptr) << 8) + (int )(*(ptr + 1))));
    } else {
        return ((*((unsigned short *)ptr)));
    }
}

int  readStructTarget(unsigned char * filePtr ,
                      unsigned char * fileEnd , ...) {
    int x = read2Target(fileEnd);
    return x;
}
