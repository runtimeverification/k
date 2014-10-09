// Copyright (c) 2014 K Team. All Rights Reserved.
#include <stdio.h>

double max(double a, double b){
    return (a<=b)?b:a;
}
double min(double a, double b){
    return (a<=b)?a:b;
}

double sqv(double x,double y) { return x*x + y*y; }

double sqs(double x,double y) { return x*x + y*y; }

double dot(double u_x, double u_y, double v_x, double v_y){
  return u_x * v_x + u_y * v_y ;
}

int horizontal_los(double s_x, double s_y)
{
  double sqS;
  double sqD;
  double E_hlos;
  sqS = sqs(s_x, s_y);
  sqD = 5.0*5.0;
  E_hlos = 1.4551915228366851806640625E-11;
  return (sqS - sqD <= E_hlos);
}

double tau_vv(double s_x, double s_y, double v_x, double v_y){
  return min(max(0.0, - dot(s_x,s_y, v_x, v_y)), 300.0*sqv(v_x, v_y));
}

double omega_vv(double s_x, double s_y, double v_x, double v_y){
  double tau;

  tau = tau_vv(s_x, s_y, v_x, v_y);
  return sqv(v_x, v_y)*sqv(s_x, s_y) + (2.0 * tau)* dot(s_x, s_y, v_x, v_y) + tau*tau - 5.0*5.0*sqv(v_x,v_y);
}

int cd2d(double s_x, double s_y, double v_x, double v_y){
  /*@  assert horizontal_losR(s_x,s_y,5.0) || omega_vvR_outDr(s_x,s_y,v_x,v_y,5.0,0.0,T) < 0 ; */
  double E_cd2d;
  E_cd2d = 1.0;
  return  (horizontal_los(s_x, s_y)) ||  (omega_vv(s_x, s_y, v_x, v_y) <= E_cd2d);
}
