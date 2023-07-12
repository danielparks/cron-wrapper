#!/bin/bash

# Close stdin, stdout, and stderr so that we test the timeout on wait() rather
# than poll() (used in other fixtures).
exec 0<&- 1<&- 2<&-

sleep 0.1
touch "$1"
