###
### * Extended Clause Database Client *
###
### Written by Florent Kirchner
### Postdoctoral Researcher, INRIA Rennes - Bretagne Atlantique, France
### Contact: florent.kirchner@lix.polytechnique.fr, www.lix.polytechnique.fr/~fkirchner
###
### This file: began on         april-2-2010,
###            last updated on  april-8-2010.
###

import sys
from socket import *

ecdb_host='localhost'
ecdb_port=7203

#
# TCP socket declaration
#

ecdb_socket = socket(AF_INET, SOCK_STREAM) # AF_UNIX?

try:
    ecdb_socket.connect((ecdb_host,ecdb_port))
except IOError:
    print "Error connecting to host",ecdb_host,"at port",ecdb_port,". Is the database started?"
    sys.exit()

#
# Read messages from stdin, send, and wait for answer.
#
while (1):
    data = raw_input('ECDB< ')
    if not data:
        break
    else:
        print "Sending message '",data,"'...",
        if not ecdb_socket.sendall(data):
            print "done."
        answer = ecdb_socket.recv(1024)  # receive up to 1K bytes
        print answer

#
# We need to send a couple of things down to the ECDB:
# - the format of the proof (Coq/PVS/HOL/...)
# - the SELECT-IN query
# - ? a 'next' command to get the following case (logically/hierarchically) ?
#
# the FORMAT of this request is tricky: do we implement a parser server-side or
# client-side? Should we stick with s-forms?
#
