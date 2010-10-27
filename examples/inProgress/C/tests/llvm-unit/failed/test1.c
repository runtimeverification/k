#include <stdio.h>
#include <altivec.h>

#if 0
vector float func(vector float vi){
#else
void func(vector float *arg){
    vector float vi = *arg;
#endif
    vector float vzero = {0.0f, 0.0f, 0.0f, 0.0f};
    vector float vres;
    vector int vmask;

    vmask = vec_sld(vec_splat_s32(0), vec_splat_s32(-1), 4);
    vi    = vec_sel(vi, vzero, (vector unsigned int)vmask);      /* (x, y, z, 0) */
    vres  = vec_madd(vi, vi, vzero);        /* (x^2, y^2, z^2, 0) */
    if(vec_all_eq(vres, vzero)) /* Is squared vec equal to the zero vec? */
    {
        vres = vec_ctf(vec_sld(vmask, vmask, 4), 0);    /* return (0 0 -1 0) */
    }
    else
    {
        vector float vtmp;
        vtmp = vec_sld(vres, vres, 4);
        vtmp = vec_add(vtmp, vres);     /* (x^2 + y^2, y^2 + z^2, z^2, x^2) */
        vtmp = vec_sld(vtmp, vtmp, 8);  /* (z^2, x^2, x^2 + y^2, y^2 + z^2) */
        vtmp = vec_add(vtmp, vres);     /* (x^2 + z^2, x^2 + y^2, x^2 + y^2 + z^2, y^2 + z^2) */
        vtmp = vec_splat(vtmp, 2);
        vtmp = vec_rsqrte(vtmp);
        vres = vec_madd(vtmp, vi, vzero);
    }
#if 0
        return vres;
#else
	*arg = vres;
#endif
}

int main(int argc, char *argv[])
{        vector float v = {0.0f, 3.0f, 1.0f, 4.0f};
        float f[4];
#if 0
        v = func(v);
#else
	func(&v);
#endif
        f[0] = ((float *) &v)[0];
        f[1] = ((float *) &v)[1];
        f[2] = ((float *) &v)[2];
        f[3] = ((float *) &v)[3];

        printf("[%f %f %f %f]\n", f[0], f[1], f[2], f[3]);

        return 0;
}

