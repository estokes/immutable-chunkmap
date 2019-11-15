#!/usr/bin/python

import subprocess
import matplotlib.pyplot as plt
import numpy as np

def run_one(bench, kind, size):
    return [ float(x) for x in subprocess.run(
        ["target/release/bench", bench, kind, size],
        stdout = subprocess.PIPE,
        check = True
    ).stdout.strip().split(b',') ]

def avg3(l):
    l.append((l.pop() + l.pop() + l.pop()) / 3.)

def run(bench, kind):
    result = {
        'insert': [],
        'insert_many': [],
        'insert_many_par': [],
        'get': [],
        'get_parallel': [],
        'remove': [],
    }
    for size in ['1000', '10000', '100000', '1000000', '10000000']:
        for j in [1, 2, 3]:
            res = run_one(bench, kind, size)
            result['insert'].append(res[1])
            result['insert_many'].append(res[2])
            result['insert_many_par'].append(res[3])
            result['get'].append(res[4])
            result['get_parallel'].append(res[5])
            result['remove'].append(res[6])
        avg3(result['insert'])
        avg3(result['insert_many'])
        avg3(result['get'])
        avg3(result['get_parallel'])
        avg3(result['remove'])
    return result
            
def plot(fname, title, xlbl, ylbl, cm, hm, btm):
    fig, ax = plt.subplots()
    labels = ['1k', '10k', '100k', '1m', '10m']
    x = np.arange(len(labels))
    width = 0.20
    rects_hm = ax.bar(x - width, hm, width, label="HashMap")
    rects_cm = ax.bar(x, cm, width, label="Chunkmap")
    rects_bt = ax.bar(x + width, btm, width, label="BtreeMap")
    ax.set_ylabel(xlbl)
    ax.set_xlabel(ylbl)
    ax.set_title(title)
    ax.set_xticks(x)
    ax.set_xticklabels(labels)
    ax.legend()
    fig.tight_layout()
    fig.savefig(fname)

results = {
    'chunkmap': {
        'ptr': run('cm', 'ptr'),
        'str': run('cm', 'str'),
    },
    'hashmap': {
        'ptr': run('hm', 'ptr'),
        'str': run('hm', 'str'),
    },
    'btreemap': {
        'ptr': run('btm', 'ptr'),
        'str': run('btm', 'str'),
    },
}

plt.rcdefaults()
plot(
    'usize_insert.png', 'insert', "ns / insert", "final size",
    results['chunkmap']['ptr']['insert'],
    results['hashmap']['ptr']['insert'],
    results['btreemap']['ptr']['insert']
)
plot(
    'usize_insert_many.png', "insert many", "ns / insert", "final size",
    results['chunkmap']['ptr']['insert_many'],
    results['hashmap']['ptr']['insert_many'],
    results['btreemap']['ptr']['insert_many']
)
plot(
    'usize_insert_many_par.png', "insert many (all cores)", "ns / insert", "final size",
    results['chunkmap']['ptr']['insert_many_par'],
    results['hashmap']['ptr']['insert_many_par'],
    results['btreemap']['ptr']['insert_many_par']
)
plot(
    'usize_remove.png', "remove", "ns / remove", "initial size",
    results['chunkmap']['ptr']['remove'],
    results['hashmap']['ptr']['remove'],
    results['btreemap']['ptr']['remove']
)
plot(
    'usize_get.png', "get", "ns / get", "size",
    results['chunkmap']['ptr']['get'],
    results['hashmap']['ptr']['get'],
    results['btreemap']['ptr']['get']
)
plot(
    'usize_get_parallel.png', "get (all cores)", "ns / get", "size",
    results['chunkmap']['ptr']['get_parallel'],
    results['hashmap']['ptr']['get_parallel'],
    results['btreemap']['ptr']['get_parallel'],
)
plot(
    'str_insert.png', 'insert', "ns / insert", "final size",
    results['chunkmap']['str']['insert'],
    results['hashmap']['str']['insert'],
    results['btreemap']['str']['insert']
)
plot(
    'str_insert_many.png', "insert many", "ns / insert", "final size",
    results['chunkmap']['str']['insert_many'],
    results['hashmap']['str']['insert_many'],
    results['btreemap']['str']['insert_many']
)
plot(
    'str_insert_many_par.png', "insert many (all cores)", "ns / insert", "final size",
    results['chunkmap']['str']['insert_many_par'],
    results['hashmap']['str']['insert_many_par'],
    results['btreemap']['str']['insert_many_par']
)
plot(
    'str_remove.png', "remove", "ns / remove", "initial size",
    results['chunkmap']['str']['remove'],
    results['hashmap']['str']['remove'],
    results['btreemap']['str']['remove']
)
plot(
    'str_get.png', "get", "ns / get", "size",
    results['chunkmap']['str']['get'],
    results['hashmap']['str']['get'],
    results['btreemap']['str']['get']
)
plot(
    'str_get_parallel.png', "get (all cores)", "ns / get", "size",
    results['chunkmap']['str']['get_parallel'],
    results['hashmap']['str']['get_parallel'],
    results['btreemap']['str']['get_parallel'],
)
