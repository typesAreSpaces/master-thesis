clear;
clf;
clc;

m = csvread('worstCase7.txt');


f = fit(m(:, 1), m(:, 2), 'poly2');
scatter(m(:, 1), m(:, 2));
hold;
plot(f);

myfit = fittype('p1*x*log(x) + p2*x + p3',...
'dependent',{'y'},'independent',{'x'},...
'coefficients',{'p1','p2', 'p3'});
f2 = fit(m(:, 1), m(:, 2), myfit);
plot(f2, 'b--');

