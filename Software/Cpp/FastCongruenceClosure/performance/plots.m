clear;
clf;
clc;

m = csvread('worstCase5.txt');


f = fit(m(:, 1), m(:, 2), 'poly2');
scatter(m(:, 1), m(:, 2));
hold;
plot(f);

myfit = fittype('a + b*x + c*x*log(x)',...
'dependent',{'y'},'independent',{'x'},...
'coefficients',{'a','b', 'c'});
f2 = fit(m(:, 1), m(:, 2), myfit);
plot(f2, 'b--');