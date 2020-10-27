# root_traits_auto

This program will eventually compute traits that can be automatically derived from the skeleton. Currently, it only outputs the average root length, computed as the total length of the skeleton divided by the number of endpoints. 

An example command:

root_traits_auto --in C:/Users/danzeng/source/repos/rootPipeline/example_root/out/root_acyclic.ply

output:

23.9749

These are in digital units, and still need to be converted to real-life measurements (e.g. mm or cm), with downsampling considered too.

