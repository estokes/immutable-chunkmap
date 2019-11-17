#!/usr/bin/python3

import json
import argparse
import subprocess
import matplotlib.pyplot as plt
import numpy as np

def run_one(exe, bench, kind, size):
    return [ float(x) for x in subprocess.run(
        [exe, bench, kind, size],
        stdout = subprocess.PIPE,
        check = True
    ).stdout.strip().split(b',') ]

def avg3(l):
    l.append((l.pop() + l.pop() + l.pop()) / 3.)

def proto():
    return {
        'insert': [],
        'insert_many': [],
        'insert_many_par': [],
        'get': [],
        'get_parallel': [],
        'remove': [],
    }

def run(exe, bench, kind):
    result = proto()
    for size in ['1000', '10000', '100000', '1000000', '10000000']:
        for j in [1, 2, 3]:
            res = run_one(exe, bench, kind, size)
            result['insert'].append(res[1])
            result['insert_many'].append(res[2])
            result['insert_many_par'].append(res[3])
            result['get'].append(res[4])
            result['get_parallel'].append(res[5])
            result['remove'].append(res[6])
        avg3(result['insert'])
        avg3(result['insert_many'])
        avg3(result['insert_many_par'])
        avg3(result['get'])
        avg3(result['get_parallel'])
        avg3(result['remove'])
    return result
            
def plot(fname, title, xlbl, ylbl, cm, hm, btm, oc):
    fig, ax = plt.subplots()
    labels = ['1k', '10k', '100k', '1m', '10m']
    x = np.arange(len(labels))
    width = 0.20
    rects_hm = ax.bar(x, hm, width, label="HashMap")
    rects_cm = ax.bar(x + width, cm, width, label="Chunkmap")
    rects_bt = ax.bar(x + width*2, btm, width, label="BtreeMap")
    rects_oc = ax.bar(x + width*3, oc, width, label="OCaml Map")
    ax.set_ylabel(xlbl)
    ax.set_xlabel(ylbl)
    ax.set_title(title)
    ax.set_xticks(x)
    ax.set_xticklabels(labels)
    ax.legend()
    fig.tight_layout()
    fig.savefig(fname)

def load_results(args):
    try:
        with open(args.data_path + '/data.json', 'r') as f:
            return json.load(f)
    except:
        return {
            'cm': {
                'ptr': proto(),
                'str': proto()
            },
            'hm': {
                'ptr': proto(),
                'str': proto()
            },
            'btm': {
                'ptr': proto(),
                'str': proto()
            },
            'oc': {
                'ptr': proto(),
                'str': proto()
            },
        }

def save_results(args, results):
    with open(args.data_path + '/data.json', 'w') as f:
        json.dump(results)

def chart(args, results):
    plt.rcdefaults()
    plot(
        args.data_path + '/usize_insert.png',
        'insert', "ns / insert", "final size",
        results['cm']['ptr']['insert'],
        results['hm']['ptr']['insert'],
        results['btm']['ptr']['insert'],
        results['oc']['ptr']['insert']
    )
    plot(
        args.data_path + '/usize_insert_many.png',
        "insert many", "ns / insert", "final size",
        results['cm']['ptr']['insert_many'],
        results['hm']['ptr']['insert_many'],
        results['btm']['ptr']['insert_many'],
        results['oc']['ptr']['insert_many']
    )
    plot(
        args.data_path + '/usize_insert_many_par.png',
        "insert many (all cores)", "ns / insert", "final size",
        results['cm']['ptr']['insert_many_par'],
        results['hm']['ptr']['insert_many_par'],
        results['btm']['ptr']['insert_many_par'],
        results['oc']['ptr']['insert_many_par']
    )
    plot(
        args.data_path + '/usize_remove.png',
        "remove", "ns / remove", "initial size",
        results['cm']['ptr']['remove'],
        results['hm']['ptr']['remove'],
        results['btm']['ptr']['remove'],
        results['oc']['ptr']['remove']
    )
    plot(
        args.data_path + '/usize_get.png',
        "get", "ns / get", "size",
        results['cm']['ptr']['get'],
        results['hm']['ptr']['get'],
        results['btm']['ptr']['get'],
        results['oc']['ptr']['get']
    )
    plot(
        args.data_path + '/usize_get_parallel.png',
        "get (all cores)", "ns / get", "size",
        results['cm']['ptr']['get_parallel'],
        results['hm']['ptr']['get_parallel'],
        results['btm']['ptr']['get_parallel'],
        results['oc']['ptr']['get_parallel']
    )
    plot(
        args.data_path + '/str_insert.png',
        'insert', "ns / insert", "final size",
        results['cm']['str']['insert'],
        results['hm']['str']['insert'],
        results['btm']['str']['insert'],
        results['oc']['str']['insert']
    )
    plot(
        args.data_path + '/str_insert_many.png',
        "insert many", "ns / insert", "final size",
        results['cm']['str']['insert_many'],
        results['hm']['str']['insert_many'],
        results['btm']['str']['insert_many'],
        results['oc']['str']['insert_many']
    )
    plot(
        args.data_path + '/str_insert_many_par.png',
        "insert many (all cores)", "ns / insert", "final size",
        results['cm']['str']['insert_many_par'],
        results['hm']['str']['insert_many_par'],
        results['btm']['str']['insert_many_par'],
        results['oc']['str']['insert_many_par']
    )
    plot(
        args.data_path + '/str_remove.png',
        "remove", "ns / remove", "initial size",
        results['cm']['str']['remove'],
        results['hm']['str']['remove'],
        results['btm']['str']['remove'],
        results['oc']['str']['remove']
    )
    plot(
        args.data_path + '/str_get.png',
        "get", "ns / get", "size",
        results['cm']['str']['get'],
        results['hm']['str']['get'],
        results['btm']['str']['get'],
        results['oc']['str']['get']
    )
    plot(
        args.data_path + '/str_get_parallel.png',
        "get (all cores)", "ns / get", "size",
        results['cm']['str']['get_parallel'],
        results['hm']['str']['get_parallel'],
        results['btm']['str']['get_parallel'],
        results['oc']['str']['get_parallel']
    )

parser = argparse.ArgumentParser(description = "run benchmarks")
parser.add_argument(
    '--run',
    required = False,
    choices = ['all', 'cm', 'hm', 'btm', 'oc']
)
parser.add_argument('--data-path', required = True)
parser.add_argument('--chart', default = False, action = 'store_const', const = True)
args = parser.parse_args()

results = load_results(args)

if args.run == 'all' or args.run == 'cm':
    results['cm']['ptr'] = run('target/release/bench', 'cm', 'ptr')
    results['cm']['str'] = run('target/release/bench', 'cm', 'str')
if args.run == 'all' or args.run == 'hm':
    results['hm']['ptr'] = run('target/release/bench', 'hm', 'ptr')
    results['hm']['str'] = run('target/release/bench', 'hm', 'str')
if args.run == 'all' or args.run == 'btm':
    results['btm']['ptr'] = run('target/release/bench', 'btm', 'ptr')
    results['btm']['str'] = run('target/release/bench', 'btm', 'str')
if args.run == 'all' or args.run == 'oc':
    results['oc']['ptr'] = run('../bench-ocaml/test', 'oc', 'ptr')
    results['oc']['str'] = run('../bench-ocaml/test', 'oc', 'str')

save_results(args, results)

if args.chart:
    chart(args, results)
