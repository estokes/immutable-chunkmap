#! /usr/bin/python3

import json
import argparse

def load_results(path):
    with open(path, 'r') as f:
        return json.load(f)

def compare(k, res0, res1, cmp0, cmp1):
    dat0 = res0[cmp0]
    dat1 = res1[cmp1]
    n = 1000;
    for i in range(0, dat0[k].length()):
        d0 = dat0[k]
        d1 = dat1[k]
        insert = d1['insert'][i] / d0['insert'][i]
        insert_many = d1['insert_many'][i] / d0['insert_many'][i]
        insert_many_par = d1['insert_many_par'][i] / d0['insert_many_par'][i]
        get = d1['get'][i] / d0['get'][i]
        get_parallel = d1['get_parallel'][i] / d0['get_parallel'][i]
        remove = d1['remove'][i] / d0['remove'][i]
        print(f'{n},{insert},{insert_many},{insert_many_par},{get},{get_parallel},{remove}')
        n = n*10
    
parser = argparse.ArgumentParser(description = "compare benchmarks")
parser.add_argument('data', nargs=2, metavar = 'FILE')
parser.add_argument('compare', nargs=2, choices = ['cm', 'hm', 'btm', 'oc'])
args = parser.parse_args()

res0 = load_results(args.data[0])
res1 = load_results(args.data[1])

compare('ptr', res0[args.compare[0]], res1[args.compare[1]])
compare('str', res0[args.compare[0]], res1[args.compare[1]])
