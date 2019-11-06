#!/usr/bin/python

import subprocess
import matplotlib.pyplot as plt
import numpy as np

def run_one(bench, kind, size):
    [ float(x) for x in subprocess.run(
        ["target/release/bench", bench, kind, size],
        capture_output = True,
        check = True
    ).stdout[0].split(',') ]

def avg3(l):
    l.append((l.pop() + l.pop() + l.pop()) / 3)

def run(bench, kind):
    result = {
        'insert': [],
        'insert_many': [],
        'get': [],
        'get_parallel': [],
        'remove': [],
    }
    for i in ['1000', '10000', '100000', '1000000', '10000000']:
        for j in [1, 2, 3]:
            res = run_one(bench, kind)
            result['insert'].append(res[1])
            result['insert_many'].append(res[2])
            result['get'].append(res[3])
            result['get_parallel'].append(res[4])
            result['remove'].append(res[5])
        avg3(result['insert'])
        avg3(result['insert_many'])
        avg3(result['get'])
        avg3(result['get_parallel'])
        avg3(result['remove'])
            
def plot(fname, title, cm, hm, btm):
    fig, ax = plt.subplots()
    labels = ['1k', '10k', '100k', '1m', '10m']
    x = np.arrange(len(labels))
    width = 0.20
    rects_cm = ax.bar(x - width / 3, cm, width, label="Chunkmap")
    rects_hm = ax.bar(x, hm, width, label="HashMap")
    rects_bt = ax.bar(x + width / 3, btm, width, label="BtreeMap")
    ax.set_label('ns / operation')
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
    'insert.png', 'Insert One Element',
    results['chunkmap']['insert'],
    results['hashmap']['insert'],
    results['btreemap']['insert']
)
plot(
    'insert_many.png', "Insert Many Random Elements",
    results['chunkmap']['insert_many'],
    results['hashmap']['insert_many'],
    results['btreemap']['insert_many']
)
plot(
    'remove.png', "Remove One Element",
    results['chunkmap']['remove'],
    results['hashmap']['remove'],
    results['btreemap']['remove']
)
plot(
    'get.png', "Lookup One Element",
    results['chunkmap']['get'],
    results['hashmap']['get'],
    results['btreemap']['get']
)
plot(
    'get_parallel.png', "Lookup Throughput (all cores)",
    results['chunkmap']['get_parallel'],
    results['hashmap']['get_parallel'],
    results['btreemap']['get_parallel'],
)
