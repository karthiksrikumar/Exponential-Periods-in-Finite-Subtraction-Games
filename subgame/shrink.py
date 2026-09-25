import json, sys
from opt import design_cost
L=json.load(open('layout_G13.json')); B=L['B']; res=L['res']; clocks=L['clocks']; clk=L['clk']
out=design_cost(B,res,clocks,clk)
print('greedy set cover on G13 layout: |S| =', out[0] if out else None)
