# Overall goal: show that if there is a $d$-connected path from $u$ to $v$, then there is an assignment of functions to nodes that equates all of the values on path

## Idea: assign functions based on whether node is mediator, confounder, or collider

<p align="center">
<img src="graphs/dconn/dconn_path.png" style="width:500px;"/>
</p>

## Issues arise if there are intersections between given $d$-connected path and descendant paths for colliders

<p align="center">
<img src="graphs/dconn/desc_path_intersects_path.png" style="width:500px;"/>
</p>

## Goal: show that if there is a $d$-connected path from $u$ to $v$, then there is a "nice" $d$-connected path from $u$ to $v$

### Nice $\iff$ no intersections between any two descendant paths _or_ between descendant path and path itself.

<p align="center">
<img src="graphs/dconn/no_overlap.png" style="width:500px;"/>
</p>
<p align="center">
<img src="graphs/dconn/two_desc_paths_no_overlap.png" style="width:500px;"/>
</p>

### How to fix "bad" $d$-connected paths

Descendant path intersects path:

<p align="center">
<img src="graphs/dconn/desc_path_intersects_path.png" style="width:500px;"/>
</p>

<p align="center">
<img src="graphs/dconn/new_path_through_desc_path.png" style="width:500px;"/>
</p>

Descendant paths intersect each other:

<p align="center">
<img src="graphs/dconn/desc_paths_intersect.png" style="width:500px;"/>
</p>

<p align="center">
<img src="graphs/dconn/new_path_through_desc_paths.png" style="width:500px;"/>
</p>
