#!/bin/bash

NODE=node
which nodejs &> /dev/null && NODE=nodejs
$NODE $@
