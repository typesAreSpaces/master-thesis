clear; clc; clf;

x = 0:1000:100000;
y1 = (8.171e-11)*x.^2 + (5.068e-06)*x + (-0.0003148);
y2 = 0.0003947 + (1.677e-07)*x + (6.083e-07)*x.*log(x);

plot(x, y1);
hold;
plot(x, y2, 'g--o');