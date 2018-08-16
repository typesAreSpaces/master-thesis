clear;
clf;
clc;

m = csvread('worstCase7_normalized.txt');

[f, gof] = fit(m(:, 1), m(:, 2), 'poly2');
scatter(m(:, 1), m(:, 2));
hold;
plot(f);

nlognfit = fittype('p1*x*log(x) + p2*x + p3',...
'dependent',{'y'},'independent',{'x'},...
'coefficients',{'p1','p2', 'p3'});
[f2, gof2] = fit(m(:, 1), m(:, 2), nlognfit);
plot(f2, 'b--');

experiment = sortrows(m', 1)';