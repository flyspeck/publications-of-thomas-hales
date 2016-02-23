NMinimize[{pinwheelarea[alpha, beta, xgamma], 0 <= xgamma, 
  xgamma <= 2 ee, 0 <= alpha, alpha <= beta, 
  beta <= Pi/5 - (alpha + beta)}, {alpha, beta, xgamma}]

NMinimize[{ljarea[alpha, beta, xgamma], 0 <= xgamma, xgamma <= 2 ee, 
  0 <= alpha, alpha <= 2 Pi/5, 0 <= beta, beta <= 2 Pi/5, 
  Pi/5 <= alpha + beta, alpha + beta <= 3 Pi/5}, {alpha, beta, xgamma}]

NMinimize[{tjarea[alpha, beta, xgamma], 0 <= xgamma, xgamma <= 2 ee, 
  0 <= alpha, 0 <= beta, alpha <= 2 Pi/5, beta <= 2 Pi/5, 
  alpha + beta <= Pi, 3 Pi/5 <= alpha + beta}, {alpha, beta, xgamma}]

NMinimize[{pinwheelarea[alpha, beta, xgamma], 0 <= xgamma, 
  xgamma <= 2 ee, 0 <= alpha, alpha <= beta, 
  beta <= Pi/5 - (alpha + beta)}, {alpha, beta, xgamma}]

NMinimize[{ljarea[alpha, beta, xgamma], 0 <= xgamma, xgamma <= 2 ee, 
   0 <= alpha, alpha <= 2 Pi/5, 0 <= beta, beta <= 2 Pi/5, 
   Pi/5 <= alpha + beta, alpha + beta <= 3 Pi/5}, {alpha, beta, 
   xgamma}];

NMinimize[{tjarea[alpha, beta, xgamma], 0 <= xgamma, xgamma <= 2 ee, 
  0 <= alpha, 0 <= beta, alpha <= 2 Pi/5, beta <= 2 Pi/5, 
  alpha + beta <= Pi, 3 Pi/5 <= alpha + beta}, {alpha, beta, xgamma}]

NMinimize[{pintarea[alpha, beta, xalpha], 0 <= xalpha, 
  xalpha <= 0.0605,(* Pi/5 *) Pi/5 <= alpha, alpha <= 2 Pi/5, 
  Pi/5 <= beta , beta <= 2 Pi/5,
  2 sigma (Sin[Pi/5 + alpha] - Sin[Pi/5 + beta]) >= 
   xalpha Sin[2 Pi/5], 3 Pi/5 <= alpha + beta}, {alpha, beta, xalpha}]

