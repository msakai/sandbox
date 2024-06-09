#!/bin/bash
nohup bash long-running-command.sh &
disown %1
