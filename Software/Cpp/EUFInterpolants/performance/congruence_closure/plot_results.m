clear;
clf;
clc;

m = csvread('results.txt');
x = m(:, 1);
y = m(:, 2);
scatter(x, y);
hold;

[quadratic, gof] = fit(x, y, 'poly2');
plot(quadratic);

nlognfit = fittype('p1*x*log(x) + p2*x + p3',...
'dependent',{'y'},'independent',{'x'},...
'coefficients',{'p1','p2', 'p3'});
[linear_log, gof2] = fit(x, y, nlognfit);
plot(linear_log, 'b--');

experiment = sortrows(m', 1)';

k = boundary(x, y);
lower_bound = k(1:find(k == 1000));
upper_bound = k(find(k == 1000):length(k));
x_lower_bound_points = x(lower_bound);
y_lower_bound_points = y(lower_bound);
x_upper_bound_points = x(upper_bound);
y_upper_bound_points = y(upper_bound);
plot(x_upper_bound_points, y_upper_bound_points);

[quadratic_upper_bound, gof_upper_bound] = fit(x_upper_bound_points, y_upper_bound_points, 'poly2');
plot(quadratic_upper_bound, 'g--');

nlognfit = fittype('p1*x*log(x) + p2*x + p3',...
'dependent',{'y'},'independent',{'x'},...
'coefficients',{'p1','p2', 'p3'});
[linear_log_upper_bound, gof2_upper_bound] = fit(x_upper_bound_points, y_upper_bound_points, nlognfit);
plot(linear_log_upper_bound, 'r--');