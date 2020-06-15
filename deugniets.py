#!/usr/bin/env python3
'''
===========================================================================
 deugniets.py v3.27-20200615 Copyright 2019-2020 by cbuijs@chrisbuijs.com
===========================================================================

 Based on: https://github.com/supriyo-biswas/adblock-dns-server
           https://github.com/cbuijs/instigator
           https://github.com/dnaeon/py-vconnector/blob/master/src/vconnector/cache.py
           https://www.reddit.com/r/Python/comments/2uik3q/expiring_inmemory_cache_module/
           https://www.bortzmeyer.org/hackathon-ietf-101.html

  This product includes the use of GeoLite2 data created by MaxMind, available from
           https://www.maxmind.com

 ToDo:
 - Work on geosteer (Geo based answers/ordering)
   - Seems to be okay as is
   - Add distance-check when no matches
 - Work on roundrobin (rrrr) seems to be random
   - Order of RRSET not maintained, dnspython weakness?
 - Finish TRIE rework of domain-based dict
   - Finish UNFILTER (+ cache) one, mix of ip/dom
   - Do geo_cache (remove cachetools)
 - Refurbish whole stack of listeners, multi-threading etc
   - Fix listening/response IP when responding (same IP out as in), IPv6
   - Fix TCP listeners
     - Might be fixed already, check/validate/test
   - Add multiple addresses/ports listen_on feature
 - Ability to disable resolution of aliases/spoofs
 - Alias based on regex
   - See instigator
 - Listen on DoT (853) and DoH (443) - SSL/Certificate config
   - Or use: https://github.com/folbricht/routedns
 - Pre-calculate ecs-prefix privacy instead everytime
   - Meh.
 - Make pruning sorted, see big_trie, apply to other *_trie as well

===========================================================================
'''

# System
import os, sys, time, gc, io
gc.enable() # Garbage collection

# Logging
import logging
logging.basicConfig(format='%(asctime)s %(levelname)s:%(message)s', datefmt='%Y-%m-%d %H:%M:%S', level=logging.INFO)
#logging.basicConfig(format='%(asctime)s %(levelname)s:%(message)s', datefmt='%Y-%m-%d %H:%M:%S', level=logging.DEBUG)

# Data
import json, struct
import configparser

# Random
import random
random.seed(os.urandom(1024))

# Threading
import threading

# Sockets and SSL
import socket
from socket import _socket
import socketserver
#import ssl

# DNSPython
import dns.rcode
import dns.flags
import dns.message
#import dns.opcode
import dns.resolver
import dns.rdatatype
import dns.exception
import dns.rdataclass
#import dns.renderer

# Process EDNS Client SubNet Option
import clientsubnetoption

# Regex
import regex
#import re as regex

# Requests for URL handling
import requests

# Use module PyTricia for CIDR/Subnet stuff
import pytricia
import netaddr

# IPy IP
from IPy import IP

# Sequencematcher
#from difflib import SequenceMatcher

# Trie
import pygtrie

# Stuff needed for DoH
import base64
#from hyper.contrib import HTTP20Adapter

# GeoIP
import geoip2.database

# CacheTools
from cachetools import LRUCache

# Cache
# https://github.com/dnaeon/py-vconnector/blob/master/src/vconnector/cache.py
# https://www.reddit.com/r/Python/comments/2uik3q/expiring_inmemory_cache_module/
from cache import CachedObject, CacheInventory

# Initialize caches
cache = CacheInventory(maxsize=8192, housekeeping=60, name='DNS-Cache', minttl=0, maxttl=0, cachelog=True)
unfilter_cache = CacheInventory(maxsize=512, housekeeping=60, name='UnFilter', minttl=0, maxttl=0, cachelog=False)

geo_cache = LRUCache(maxsize=8192)

check_cache_trie = pygtrie.StringTrie(separator='.')
check_cache_size = 8192

#big_trie = pygtrie.StringTrie(separator='.')
#big_trie_size = 512

# Lists
wl_dom = {}
bl_dom = {}
wl_ip4 = pytricia.PyTricia(32, socket.AF_INET)
bl_ip4 = pytricia.PyTricia(32, socket.AF_INET)
wl_ip6 = pytricia.PyTricia(128, socket.AF_INET6)
bl_ip6 = pytricia.PyTricia(128, socket.AF_INET6)
wl_rx = {}
bl_rx = {}
wl_geo = {}
bl_geo = {}
alias = {}
forwarder = {}
beingchecked = set()
beingspoofed = set()
ul_dom = {}
ul_ip4 = pytricia.PyTricia(32, socket.AF_INET)
ul_ip6 = pytricia.PyTricia(128, socket.AF_INET6)

blacklisted_state = {}
blacklisted_state[True] = 'BLACKLISTED'
blacklisted_state[False] = 'WHITELISTED'
blacklisted_state[None] = 'NOT-LISTED'

command_acl4 = pytricia.PyTricia(32, socket.AF_INET)
command_acl6 = pytricia.PyTricia(128, socket.AF_INET6)

command_acl4['127.0.0.1/32'] = True
command_acl6['0::1/128'] = True

private4 = pytricia.PyTricia(32, socket.AF_INET)
private6 = pytricia.PyTricia(128, socket.AF_INET6)

# vars
dummy = '#!#!DUMMY!#!#'

# Domain Regex
#is_dom = regex.compile('(?=^.{1,253}[a-z][\.]*$)(^((?!-)[a-z0-9_-]{0,62}[a-z0-9]\.)*(xn--[a-z0-9-]{1,59}|[a-z]{2,63})[\.]*$)', regex.I) # Includes underscore
is_dom = regex.compile('(?=^.{1,253}[a-z][\.]*$)(^((?!-)[a-z0-9\._-]{0,62}[a-z0-9]\.)*(xn--[a-z0-9-]{1,59}|[a-z]{2,63})[\.]*$)', regex.I) # Includes underscore

# Domain words
is_domword = regex.compile('^\*[a-z0-9\-]+$', regex.I)

# IP Regexes
ip_rx4 = '((25[0-5]|2[0-4][0-9]|1[0-9]{2}|[1-9]?[0-9])(\.(25[0-5]|2[0-4][0-9]|1[0-9]{2}|[1-9]?[0-9])){3}(/(3[0-2]|[12]?[0-9]))*)'
ip_rx6 = '(((:(:[0-9a-f]{1,4}){1,7}|::|[0-9a-f]{1,4}(:(:[0-9a-f]{1,4}){1,6}|::|:[0-9a-f]{1,4}(:(:[0-9a-f]{1,4}){1,5}|::|:[0-9a-f]{1,4}(:(:[0-9a-f]{1,4}){1,4}|::|:[0-9a-f]{1,4}(:(:[0-9a-f]{1,4}){1,3}|::|:[0-9a-f]{1,4}(:(:[0-9a-f]{1,4}){1,2}|::|:[0-9a-f]{1,4}(::[0-9a-f]{1,4}|::|:[0-9a-f]{1,4}(::|:[0-9a-f]{1,4}))))))))|(:(:[0-9a-f]{1,4}){0,5}|[0-9a-f]{1,4}(:(:[0-9a-f]{1,4}){0,4}|:[0-9a-f]{1,4}(:(:[0-9a-f]{1,4}){0,3}|:[0-9a-f]{1,4}(:(:[0-9a-f]{1,4}){0,2}|:[0-9a-f]{1,4}(:(:[0-9a-f]{1,4})?|:[0-9a-f]{1,4}(:|:[0-9a-f]{1,4})))))):(25[0-5]|2[0-4][0-9]|1[0-9]{2}|[1-9]?[0-9])(\.(25[0-5]|2[0-4][0-9]|1[0-9]{2}|[1-9]?[0-9])){3})(/(12[0-8]|1[01][0-9]|[1-9]?[0-9]))*)'
is_ip4 = regex.compile('^' + ip_rx4 + '$', regex.I)
is_ip6 = regex.compile('^' + ip_rx6 + '$', regex.I)
is_ip = regex.compile('^(' + ip_rx4 + '|' + ip_rx6 + ')$', regex.I)

# IP Arpa Regexes
ip4arpa_rx = '([0-9]{1,3}\.){4}in-addr'
ip6arpa_rx = '([0-9a-f]\.){32}ip6'
ip4arpa = regex.compile('^' + ip4arpa_rx + '\.arpa[\.]*$', regex.I)
ip6arpa = regex.compile('^' + ip6arpa_rx + '\.arpa[\.]*$', regex.I)
iparpa = regex.compile('^(' + ip4arpa_rx + '|' + ip6arpa_rx + ')\.arpa[\.]*$', regex.I)

# Returncodes
is_rc = regex.compile('^(NODATA|NOERROR|NXDOMAIN|RANDOM|REFUSED|SERVFAIL)$', regex.I)

# Dom
is_dom_txt = '^((?!-)[a-z0-9_-]{0,62}[a-z0-9]\.)*(xn--[a-z0-9-]{1,59}|[a-z]{2,63})[\.]*' # Includes underscore

# Alias
is_alias = regex.compile(is_dom_txt + '\s*=\s*.+$', regex.I)

# Forwarder
is_forwarder = regex.compile(is_dom_txt + '\s*>\s*.+$', regex.I)

# TTL
is_ttl = regex.compile(is_dom_txt + '\s*!\s*[0-9]+$', regex.I)

# Test if alias/forwarder/ttl
is_aft = regex.compile('^(\+|.*[=>!]).*$', regex.I)

# Unfilter
is_unfilter = regex.compile('^\+.*$', regex.I)

# Is DoH or DoT
#is_dox = regex.compile('^(dns|https|tls)://(?!(do[ht]|ip(v)*)[46]\.).*$', regex.I)
is_dox = regex.compile('^(dn|http|tl)s://.*$', regex.I)
is_dox4 = regex.compile('^(dn|http|tl)s://(do[ht]|ip(v)*)4\..*$', regex.I)
is_dox6 = regex.compile('^(dn|http|tl)s://(do[ht]|ip(v)*)6\..*$', regex.I)

# GEO
is_geo = regex.compile('^@([a-z\/\:\s]+|[0-9]+)$', regex.I)

# Regex
is_regex = regex.compile('^/.*/$', regex.I)

#####################################################################

# Replace socket.getaddrinfo with caching version to speedup requests/urllib/abuseipdb
def _getaddrinfo(host, port=53, family=0, type=0, proto=0, flags=0):
    #logging.debug('GETADDRINFO: {0} {1} {2} {3} {4} {5}'.format(host, port, family, type, proto, flags))

    cachename = '{0}/{1}/GETADDRINFO'.format(host, port)

    count = 0
    while count < config['retry_count'] and cachename in beingchecked:
        count += 1
        #logging.debug('{0}-BLACKLIST-SLEEP: {1} (#{2})'.format(valuetype, testvalue, count))
        time.sleep(config['retry_wait'])

    beingchecked.add(cachename)

    result = cache.get(cachename, None)

    if result is None:
        if is_ip.search(host):
            if host.find(':') > -1:
                result = [(10, 1, 6, '', (host, port, 0, 0))]
            else:
                result = [(2, 1, 6, '', (host, port))]

        else:
            try:
                result = _socket.getaddrinfo(host, port, family, type, proto, flags)
            except BaseException as err:
                result = None
                logging.error('GETADDRINFO-ERROR: {0} - {1}'.format(host, err))

        if result:
            ips = list((map(lambda x: x[4][0], result)))
            if ips:
                cache.add(obj=CachedObject(name=cachename, obj=result, ttl=604800)) # 7 Days

    beingchecked.discard(cachename)

    return result

socket.getaddrinfo = _getaddrinfo

#####################################################################

def setup_nameservers():
    '''Setup NameServers to Forward to'''
    dns.resolver.default_resolver = dns.resolver.Resolver(configure=False)
    dns.resolver.default_resolver.nameservers = ['8.8.8.8', '8.8.4.4', '2001:4860:4860::8888', '2001:4860:4860::8844']
    dns.resolver.default_resolver.port = 53
    dns.resolver.default_resolver.use_edns(0, 0, 1220) # DNSFLag Day 2020 advice. 1220:ipv6, 1480:ipv4
    dns.resolver.default_resolver.timeout = 5
    dns.resolver.default_resolver.lifetime = 15


def get_config(config, conffile):
    '''Get config'''
    section = 'DEUGNIETS'

    pconfig = configparser.ConfigParser()
    pconfig.sections()
    pconfig.read(conffile)

    for key in pconfig[section]:
        try:
            config[key.lower()] = json.loads(pconfig.get(section, key))
            logging.debug('CONFIG-{0}: \"{1}\" = \"{2}\"'.format(str(type(config[key])).upper().split('\'')[1], key.lower(), config[key]))
        except BaseException as err:
            logging.error('CONFIG-ERROR: Problem parsing \"{0}\" - {1}'.format(key.lower(), err))
            logging.error('ABORT!')
            sys.exit(1)

    return config


def add_list(domlist, addlist, comment):
    for dom in addlist:
        for entry in dom.split(','):
            if is_dom.search(entry) and (dom not in domlist):
                logging.debug('ADD-LIST: {0} ({1})'.format(entry, comment))
                domlist[dom] = entry
    return domlist


def undom(domlist1, domlist2, listname, onlysub):
    name1, name2 = listname.split('-')[0:2]
    if domlist1 and domlist2:
        logging.info('UNDOM [{0}]: Optimizing List, removing matching sub-domains ...'.format(listname))
        newdomlist = {}
        beforecount = len(domlist1)
        for dom in domlist1:
            match = check_dom('NAME', dom, domlist2, False, False, False)
            if match:
                if onlysub and match == dom:
                    match = False

            if match is False:
                newdomlist[dom] = domlist1[dom]
            else:
                logging.info('UNDOM [{0}]: Removed {1} from {2}, matches {3} {4}'.format(listname, dom, name1, name2, match))

        aftercount = len(newdomlist)
        logging.info('UNDOM [{0}]: Went from {1} to {2} entries ({3})'.format(listname, beforecount, aftercount, aftercount - beforecount))
        return newdomlist

    return domlist1


def unreg(domlist, bigrx, listname):
    if domlist and bigrx and bigrx != regex.compile(dummy):
        logging.info('UNREG [{0}]: Optimizing List, removing REGEX matches ...'.format(listname))
        remove = filter(bigrx.search, domlist.keys())
        newdomlist = {}
        beforecount = len(domlist)
        for dom in domlist:
            if dom in remove:
                logging.info('UNREG [{0}]: Removed {1}'.format(listname, dom))
            else:
                newdomlist[dom] = domlist[dom]
        
        aftercount = len(newdomlist)
        logging.info('UNREG [{0}]: Went from {1} to {2} entries ({3})'.format(listname, beforecount, aftercount, aftercount - beforecount))

        return newdomlist

    return domlist

    #if domlist and bigrx and bigrx != regex.compile(dummy):
    #    logging.info('UNREG [{0}]: Optimizing List, removing REGEX matches ...'.format(listname))
    #    newdomlist = {}
    #    beforecount = len(domlist)
    #    for dom in domlist:
    #        match = bigrx.search(dom.rstrip('.'))
    #        if match:
    #            logging.debug('UNREG [{0}]: Removed {1}'.format(listname, dom))
    #        else:
    #            newdomlist[dom] = domlist[dom]
    #
    #    aftercount = len(newdomlist)
    #    logging.info('UNREG [{0}]: Went from {1} to {2} entries ({3})'.format(listname, beforecount, aftercount, aftercount - beforecount))
    #    return newdomlist
    #
    #return domlist


def unip(iplist1, iplist2, ip6, listname, allowsame):
    name1, name2 = listname.split('-')[0:2]
    if iplist1 and iplist2:
        if ip6:
            fam = 'IPV6'
            newiplist = pytricia.PyTricia(128, socket.AF_INET6)
            newiplist2 = pytricia.PyTricia(128, socket.AF_INET6)
        else:
            fam = 'IPV4'
            newiplist = pytricia.PyTricia(32, socket.AF_INET)
            newiplist2 = pytricia.PyTricia(32, socket.AF_INET)

        logging.info('UNIP-{0} [{1}]: Optimizing List, removing matching subnets ...'.format(fam, listname))

        beforecount = len(iplist1)
        for ip in iplist1:
            match = False
            if ip in iplist2:
                match = iplist2.get_key(ip)
                if allowsame and ip == match:
                    match = False
           
            if match is False:
                newiplist[ip] = iplist1[ip]
            else:
                logging.info('UNIP-{0} [{1}]: Removed {2} {3} matches {4} {5}'.format(fam, listname, ip, name1, match, name2))

        aftercount = len(newiplist)
        logging.info('UNIP-{0} [{1}]: Went from {2} to {3} entries ({4})'.format(fam, listname, beforecount, aftercount, aftercount - beforecount))

        return agg_ip(newiplist, listname, fam)

    return iplist1
        
# Aggregate IP list
def agg_ip(iplist, listname, fam):
    logging.info('AGGREGATE-{0} [{1}]: Aggregating List ...'.format(fam, listname))

    if fam == 'IPV4':
        new = pytricia.PyTricia(32, socket.AF_INET)
    else:
        new = pytricia.PyTricia(128, socket.AF_INET6)

    for ip in list(map(str, netaddr.cidr_merge(list(iplist)))):
        new[ip] = True
        if ip not in iplist:
            logging.info('AGGREGATE-{0} [{1}]: Removed {2} due to summarization'.format(fam, listname, ip))
           
    beforecount = len(iplist)
    aftercount = len(new)
    logging.info('AGGREGATE-{0} [{1}]: Went from {2} to {3} entries ({4})'.format(fam, listname, beforecount, aftercount, aftercount - beforecount))

    return new


def make_doms(domlist):
    if domlist:
        newdomlist = set()
        for dom in domlist:
            if is_dom.search(dom):
                newdomlist.add(make_dom(dom))

        return newdomlist
    return domlist


def make_dom(domname):
    return '{0}.'.format(domname.strip('.').lower())


#def similar(x, y):
#    return int(SequenceMatcher(None, x, y).ratio() * 100)


def encode_0x20(st):
    if config['0x20']:
        return ''.join(random.choice((str.upper, str.lower))(c) for c in st)

    return st.lower()


def cleansplit(s):
    return regex.split('\s*#\s*', s)[0].strip().rstrip('!')


def make_trie(dlist, listname, keepval):
    logging.info('MAKE-TRIE: {0}'.format(listname))

    new_trie = pygtrie.StringTrie(separator='.')
    for key in dlist.keys():
        if keepval:
            new_trie[key[::-1]] = dlist.get(key, None)
        else:
            new_trie[key[::-1]] = None

    logging.info('MAKE-TRIE: {0} = {1} Entries'.format(listname, len(new_trie)))

    return new_trie


def read_list(filenames, listname, domlst, ip4lst, ip6lst, rxlst, unlst, unip4, unip6, geolst, alst, flst):
    '''Get lists from either file or URL'''
    for filename in filenames:

        logging.info('PROCESS-LIST: {0} ...'.format(filename))

        ftype = False
        if filename.find(':') > -1:
            ft = filename.split(':')[0].upper()
            if ft in ('IP', 'IP4', 'IP6','DOM', 'DOMWORD', 'GEO', 'ALIAS', 'FORWARD', 'TTL', 'UNFILTER', 'RX'):
                filename = ':'.join(filename.split(':')[1:])
                ftype = ft
                logging.info('PROCESS-LIST ({0}): {1}-LIST ...'.format(filename, ftype))
        else:
                logging.info('PROCESS-LIST ({0}): GENERIC-LIST ...'.format(filename))
          

        lname = '{0}:{1}'.format(listname, filename)
        lines = get_lines(filename, listname)

        if lines:
            if ftype:
                cleanlines = lines
            else:
                logging.info('PROCESS-LIST ({0}): Clean-up of {1} lines ...'.format(lname, len(lines)))
                cleanlines = set(map(cleansplit, lines))

            #cleanlines = set()
            #for line in list(filter(None, lines)):
            #    cleanline = regex.split('\s*#\s*', line)[0].strip().rstrip('!') # Strip comments and line-feeds
            #    if cleanline and cleanline not in cleanlines:
            #        cleanlines.add(cleanline)

            logging.info('PROCESS-LIST ({0}): Processing {1} lines (out of {2}) ...'.format(lname, len(cleanlines), len(lines)))

            oldtotal = len(domlst) + len(ip4lst) + len(ip6lst) + len(rxlst) + len(unlst) + len(unip4) + len(unip6) + len(geolst) + len(alst) + len(flst)
            
            if ftype is False or ftype in ('IP', 'IP4', 'IP6'):
                before = len(ip4lst) + len(ip6lst)
                logging.info('PROCESS-LIST ({0}): Getting IPs...'.format(lname))
                if ftype in ('IP', 'IP4'):
                    for entry in list(filter(None, filter(is_ip4.search, cleanlines))):
                        ip4lst[entry] = entry

                if ftype in ('IP', 'IP6'):
                    for entry in list(filter(None, filter(is_ip6.search, cleanlines))):
                        ip6lst[addzero(entry)] = entry

                logging.info('PROCESS-LIST ({0}): Fetched {1} IPs'.format(lname, (len(ip4lst) + len(ip6lst)) - before))


            if ftype is False or ftype == 'DOM':
                before = len(domlst)
                logging.info('PROCESS-LIST ({0}): Getting DOMAINs...'.format(lname))
                domlst.update(dict.fromkeys(list(map(make_dom, filter(None, filter(is_dom.search, cleanlines)))), 'Domain'))
                logging.info('PROCESS-LIST ({0}): Fetched {1} DOMAINs'.format(lname, len(domlst) - before))


            if ftype is False or ftype == 'DOMWORD':
                before = len(rxlst)
                logging.info('PROCESS-LIST ({0}): Getting DOMWORDs...'.format(lname))
                for entry in list(filter(None, filter(is_domword.search, cleanlines))):
                    try:
                        domwordrx = '^(.*[\.\-])*{0}([\.\-].*)*$'.format(entry.lstrip('*'))
                        rxlst[domwordrx] = regex.compile(domwordrx, regex.I)
                        logging.info('DOMWORD: {0} -> {1}'.format(entry, domwordrx))
                    except BaseException as err:
                        logging.warning('LIST [{0}]: Invalid Syntax: \"{1}\" - {2}'.format(lname, entry, err))

                logging.info('PROCESS-LIST ({0}): Fetched {1} DOMWORDs'.format(lname, len(rxlst) - before))


            if ftype is False or ftype == 'GEO':
                before = len(geolst)
                logging.info('PROCESS-LIST ({0}): Getting GEOs...'.format(lname))
                for entry in list(filter(None, filter(is_geo.search, cleanlines))):
                    entry = entry.lstrip('@')
                    loc = False
                    if entry.find(':') > -1:
                        loc, entry = entry.split(':')[0:2]
                        if loc not in ('CONTINENT', 'COUNTRY', 'AREA', 'CITY'):
                            logging.error('PROCESS-LIST ({0}): Invalid GEO type {1} ({1}:{2})'.format(lname, loc, entry))
                            loc = False

                    if loc:
                        geolst['{0}:{1}'.format(loc, regex.sub('[^a-zA-Z0-9]+', '', entry.upper()))] = entry
                    else:
                        geolst[regex.sub('[^a-zA-Z0-9\/]+', '', entry.upper())] = entry

                logging.info('PROCESS-LIST ({0}): Fetched {1} GEOs'.format(lname, len(geolst) - before))


            if ftype is False or ftype == 'ALIAS':
                before = len(alst)
                logging.info('PROCESS-LIST ({0}): Getting ALIASes...'.format(lname))
                for entry in list(filter(None, filter(is_alias.search, cleanlines))):
                    datatype = False
                    domain, value = get_value(entry, '=', is_rc.search, False)
                    if value is False:
                        domain, value = get_value(entry, '=', is_ip4.search, False)
                        domain, value = get_value(entry, '=', is_ip6.search, value)
                        if value is False:
                            domain, value = get_value(entry, '=', is_dom.search, False)

                        if value:
                            value = value.lower()
                    else:
                        value = value.upper()

                    if domain and value:
                        domain = make_dom(domain)
                        logging.debug('SPOOF: {0} redirect to {1}'.format(domain, ', '.join(value.split(','))))
                        alst[domain] = value
                    else:
                        logging.warning('LIST [{0}]: Invalid ALIAS Syntax: \"{1}\"'.format(lname, entry))

                logging.info('PROCESS-LIST ({0}): Fetched {1} ALIASes'.format(lname, len(alst) - before))


            if ftype is False or ftype == 'FORWARD':
                before = len(flst)
                logging.info('PROCESS-LIST ({0}): Getting FORWARDers...'.format(lname))
                for entry in list(filter(None, filter(is_forwarder.search, cleanlines))):
                    domain, value = get_value(entry, '>', is_ip.search, False)
                    if domain and value:
                        domain = make_dom(domain)
                        logging.debug('FORWARDER: {0} forward to {1}'.format(domain, ', '.join(value.lower().split(','))))
                        flst[domain] = value.lower()
                    else:
                        logging.warning('LIST [{0}]: Invalid FORWARDER Syntax: \"{1}\"'.format(lname, entry))

                logging.info('PROCESS-LIST ({0}): Fetched {1} FORWARDers'.format(lname, len(flst) - before))


            if ftype is False or ftype == 'UNFILTER':
                before = len(unlst) + len(unip4) + len(unip6)
                logging.info('PROCESS-LIST ({0}): Getting UNFILTERs...'.format(lname))
                for entry in list(filter(None, filter(is_unfilter.search, cleanlines))):
                    domip = entry.lstrip('+')
                    if is_dom.search(domip):
                        logging.debug('UNFILTER-DOM: {0}'.format('{0}.'.format(domip.strip('.').lower())))
                        unlst[make_dom(domip)] = entry

                    elif is_ip4.search(domip):
                        logging.debug('UNFILTER-IPV4: {0}'.format(domip))
                        try:
                            unip4[domip] = entry
                        except BaseException as err:
                            logging.warning('LIST [{0}]: Invalid Syntax: \"{1}\" - {2}'.format(lname, entry, err))

                    elif is_ip6.search(domip):
                        logging.debug('UNFILTER-IPV6: {0}'.format(domip))
                        try:
                            unip6[domip] = entry
                        except BaseException as err:
                            logging.warning('LIST [{0}]: Invalid Syntax: \"{1}\" - {2}'.format(lname, entry, err))

                    else:
                        logging.warning('LIST [{0}]: Invalid UnFilter Syntax: \"{1}\"'.format(lname, entry))

                logging.info('PROCESS-LIST ({0}): Fetched {1} UNFILTERs'.format(lname, (len(unlst) + len(unip4) + len(unip6)) - before))


            if ftype is False or ftype == 'RX':
                before = len(rxlst)
                logging.info('PROCESS-LIST ({0}): Getting REGEXes...'.format(lname))
                clines = cleanlines
                if ftype is False:
                    clines = list(filter(None, filter(is_regex.search, cleanlines)))
                
                for entry in clines:
                    entry = entry.strip('/')
                    try:
                        rxlst[entry] = regex.compile(entry, regex.I) # To test/validate
                    except BaseException as err:
                        logging.warning('LIST [{0}]: Invalid Syntax: \"{1}\" - {2}'.format(lname, entry, err))

                logging.info('PROCESS-LIST ({0}): Fetched {1} REGEXes'.format(lname, len(rxlst) - before))


            newtotal = len(domlst) + len(ip4lst) + len(ip6lst) + len(rxlst) + len(unlst) + len(unip4) + len(unip6) + len(geolst) + len(alst) + len(flst)
            total = newtotal - oldtotal

            logging.info('PROCESS-LIST ({0}): Added {1} new entries (Skipped {2} comment/overlap/duplicate/empty/invalid)...'.format(lname, total, len(cleanlines) - total))

    return domlst, ip4lst, ip6lst, rxlst, unlst, unip4, unip6, geolst, alst, flst

def get_value(entry, sepp, filt, addvalue):
    elements = list(regex.split('\s*{0}\s*'.format(sepp), entry))
    if elements:
        param = elements[0].lower()
        if param:
            values = ','.join(list(filter(None, filter(filt, regex.split('\s*,\s*', ','.join(elements[1:]))))))
            if values:
                if addvalue:
                    values = '{0},{1}'.format(addvalue, values)
                return param, values

    return False, False


def addzero(entry):
    if entry.startswith(':'):
        entry = '0{0}'.format(entry)
    return entry


def get_lines(filename, listname):
    '''Get all lines from file or URL'''
    logging.info('GET-LINES: {0} - {1}'.format(filename, listname))
    lines = False

    if filename.startswith('http://') or filename.startswith('https://'):
        logging.info('FETCH: Downloading \"{0}\" from URL \"{1}\" ...'.format(listname, filename))
        headers = {'User-Agent': 'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/63.0.3239.132 Safari/537.36'}
        #headers = {'User-Agent': config['useragent']}
        try:
            r = requests.get(filename, timeout=10, headers=headers, allow_redirects=True)
            if r.status_code == 200:
                #lines = uniq(r.text.splitlines(0), filename)
                lines = r.text.splitlines(0)
            else:
                logging.error('ERROR: Unable to download from \"{0}\" ({1})'.format(filename, r.status_code))

        except BaseException as err:
            logging.error('ERROR: Unable to download from \"{0}\" ({1})'.format(filename, err))

    elif file_exist(filename, False):
        logging.info('FETCH: Fetching \"{0}\" from file \"{1}\" ...'.format(listname, filename))
        try:
            f = io.open(filename, 'r')
            #lines = uniq(f.read().splitlines(0), filename)
            lines = f.read().splitlines(0)
            f.close()

        except BaseException as err:
            logging.error('ERROR: Unable to open/read/process file \"{0}\" - {1}'.format(filename, err))
            return False

    #if lines:
    #    logging.info('GET-LINES [{0}]: Fetched {1} lines from {2}'.format(listname, len(lines), filename))

    return lines


def uniq(lst, lstname):
    return list(filter(None, list(dict.fromkeys(lst, lstname))))


def file_exist(file, isdb):
    '''Check if file exists and what its age is'''
    if file:
        try:
            if os.path.isfile(file):
                fstat = os.stat(file)
                fsize = fstat.st_size
                if fsize > 0: # File-size must be greater then zero
                    mtime = int(fstat.st_mtime)
                    currenttime = int(time.time())
                    age = int(currenttime - mtime)
                    logging.debug('FILE-EXIST: {0} = {1} seconds old'.format(file, age))
                    return age
                else:
                    logging.debug('FILE-EXIST: {0} is zero size'.format(file))

        except BaseException as err:
            logging.error('FILE-EXIST-ERROR: {0}'.format(err))
            return False

    return False


def roundrobin(lst, force):
    '''Rotate list'''
    if lst:
        if force or config['roundrobin']:
            if config['randomroundrobin']:
                r = random.randint(1, len(lst))
            else:
                r = 1

            return list(filter(None, lst[r:] + lst[:r]))

    return list(lst)


# convert to in-addr/ip6.arpa
def rev_ip(ip, delimiter):
    '''Convert IP into an rev-arpa domain'''
    revip = False
    eip = expand_ip(ip)
    prefix = False

    if '/' in eip:
        eip, prefix = regex.split('/', eip)[0:2]
    else:
        if is_ip4.search(eip):
            prefix = '32'
        elif is_ip6.search(eip):
            prefix = '128'

    if prefix:
        prefix = int(prefix)
        if is_ip4.search(eip):
            #if prefix in (8, 16, 24, 32):
            if int(prefix) % 8 == 0:
                revip = '{0}.in-addr.arpa.'.format('.'.join(eip.split('.')[0:int(prefix / 8)][::-1]))
                
            elif delimiter:
                octs = eip.split('.')[::-1]
                octs[3 - int(prefix / 8)] = octs[3 - int(prefix / 8)] + delimiter + str(prefix)
                revip = '.'.join(octs[3 - int(prefix / 8):]) + '.in-addr.arpa.'
                revip = '{0}.in-addr.arpa.'.format('.'.join(octs[3 - int(prefix / 8):]))

        elif is_ip6.search(eip):
            #if prefix in (4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 68, 72, 76, 80, 84, 88, 92, 96, 100, 104, 108, 112, 116, 120, 124, 128):
            if int(prefix) % 4 == 0:
                revip = '{0}.ip6.arpa.'.format('.'.join(filter(None, regex.split('(.)', regex.sub(':', '', eip))))[0:int(prefix / 4) * 2][::-1].strip('.'))
            elif delimiter:
                nibs = filter(None, regex.split('(.)', regex.sub(':', '', eip)))[::-1]
                nibs[31 - int(prefix / 4)] = nibs[31 - int(prefix / 4)] + delimiter + str(prefix)
                revip = '{0}.ip6.arpa.'.format('.'.join(nibs[31 - int(prefix /4):]))

    return revip


def expand_ip(ip):
    '''Expand IPv6 addresses'''
    return str(IP(str(ip)).strFullsize())

    # !!!! Remove below
    #ip = str(ip)
    #if not is_ip6.search(ip):
    #    return ip

    #new_ip = ip

    #prefix = False
    #if '/' in new_ip:
    #    new_ip, prefix = new_ip.split('/')[0:2]
    #    if new_ip.endswith(':'):
    #        new_ip = '{0}0'.format(new_ip)

    #if '::' in new_ip:
    #    padding = 9 - new_ip.count(':')
    #    new_ip = new_ip.replace(('::'), ':' * padding)

    #parts = new_ip.split(':')
    #for part in range(8):
    #    parts[part] = str(parts[part]).zfill(4)

    #new_ip = ':'.join(parts)

    #if prefix:
    #    new_ip = '{0}/{1}'.format(new_ip, prefix)

    #logging.debug('IPV6-EXPANDER: {0} -> {1}'.format(ip, new_ip))

    #return new_ip


def compress_ip(ip):
    '''Compress IPv6 addresses'''
    return str(IP(str(ip)).strCompressed())


# DO SOMETHING WITH THIS !!!!
def is_formerr(rtype, value, qtype):
    '''Check if weird'''
    if config['filtering'] and config['blockweird']:
        #logging.debug('{0}-FORMERR-CHECK: {1}/{2}'.format(rtype, value, qtype))
        value = str(value)

        # Request qname
        if rtype in ('CHAIN-NAME', 'REQUEST'):
            # Root
            if value == '.' and config['blockroot']:
                logging.warning('{0}-FORMERR-HIT: {1}/{2} - Root'.format(rtype, value, qtype))
                return True

            # Name is an IP
            if is_ip.search(value):
                logging.warning('{0}-FORMERR-HIT: {1}/{2} - Name is IP-Address'.format(rtype, value, qtype))
                return True

            # Not a domain-name
            if value != '.':
                if not is_dom.search(value):
                    logging.warning('{0}-FORMERR-HIT: {1}/{2} - Name not a valid Domain-Name'.format(rtype, value, qtype))
                    return True

                # Undotted name
                if value.strip('.').count('.') < 1:
                    logging.warning('{0}-FORMERR-HIT: {1}/{2} - Name not dotted'.format(rtype, value, qtype))
                    return True
    
            # PTR records that do not comply with IP-Addresses
            if qtype == 'PTR' and (not iparpa.search(value)):
                logging.warning('{0}-FORMERR-HIT: {1}/{2} - PTR name not in ip-arpa syntax'.format(rtype, value, qtype))
                return True

            # Reverse-lookups are not PTR records
            if qtype != 'PTR' and (iparpa.search(value)):
                logging.warning('{0}-FORMERR-HIT: {1}/{2} - Non-PTR name with ip-arpa request'.format(rtype, value, qtype))
                return True

            # SRV records where qname has more then two underscores
            if qtype == 'SRV' and value.count('_') > 2:
                logging.warning('{0}-FORMERR-HIT: {1}/{2} - Too many underscores (>2)'.format(rtype, value, qtype))
                return True

            # Non-SRV records with underscores in qname
            if qtype != 'SRV' and value.count('_') > 0:
                logging.warning('{0}-FORMERR-HIT: {1}/{2} - Non-SRV Underscore'.format(rtype, value, qtype))
                return True

        # Response Data
        elif rtype in ('RESPONSE'):
            # PTR record pointing to an IP
            if qtype in ('A', 'AAAA') and (not is_ip.search(value)):
                logging.warning('{0}-FORMERR-HIT: {1}/{2} - Address data not an IP-Address'.format(rtype, value, qtype))
                return True

            # Data not a domain
            if qtype in ('CNAME', 'NS', 'PTR') and ((not is_dom.search(value)) or is_ip.search(value)):
                logging.warning('{0}-FORMERR-HIT: {1}/{2} - Data not a domain-name'.format(rtype, value, qtype))
                return True

            # Data of response is an arpa domain, technically not wrong, just weird
            if iparpa.search(value):
                logging.warning('{0}-FORMERR-HIT: {1}/{2} - Data is ip-arpa syntax'.format(rtype, value, qtype))
                return True

            # Underscores
            if value.count('_') > 0:
                logging.warning('{0}-FORMERR-HIT: {1}/{2} - Data contains Underscore(s)'.format(rtype, value, qtype))
                return True

    return False


def trie_cache_put(cachename, ttl, rv):
    cachename = regex.sub('\.+', '.', regex.sub('/', '.', cachename))
    if cachename[::-1] not in cache_trie:
        cache_trie[cachename[::-1]] = int(time.time() + ttl), rv
        logging.info('CACHE: Cached \"{0}\" (TTL:{1}) - {2} Entries'.format(cachename, ttl, len(cache_trie)))
        prune = int(time.time()) % 60
        while prune in (0, 30) and len(cache_trie) > cache_trie_size: # Housekeeping every 30 seconds
            first = list(cache_trie.keys())[0]
            try:
                oldexpire, oldrv = cache_trie.pop(first)
                logging.info('CACHE: Pruned \"{0}\" (TTL:{1}) - {2} Entries left)'.format(first[::-1], int(oldexpire - time.time()), len(cache_trie)))
            except:
                pass

    else:
        logging.info('CACHE: NOT Cached \"{0}\" - Already exists'.format(cachename))

    return None


def trie_cache_get(cachename):
    cachename = regex.sub('\.+', '.', regex.sub('/', '.', cachename))
    expire = 0
    rv = None
    parent = None
    if cachename[::-1] in cache_trie:
        expire, rv = cache_trie.get(cachename[::-1])
    elif config['parent_cache_hit']:
        parent = cache_trie.longest_prefix(cachename[::-1]).key or False
        if parent:
            parent_expire, parent_rv = cache_trie.get(parent)
            if parent_rv[0] != 0:
                expire = parent_expire
                rv = parent_rv
            
    if rv:
        left = int(expire - time.time())
        if left > 0:
            if parent:
                logging.info('CACHE: Retrieved from parent \"{0}\" -> \"{1}\" (TTL:{2})'.format(cachename, parent[::-1], left))
            else:
                logging.info('CACHE: Retrieved \"{0}\" (TTL:{1})'.format(cachename, left))
            return left, rv
        elif not parent:
            try:
                oldttl, oldrv = cache_trie.pop(cachename)
                logging.info('CACHE: Expired \"{0}\" (TTL:{1})'.format(cachename, left))
            except:
                pass

    return 0, None


def is_blacklisted(qname, value, valuetype, checkip):
    '''Check if blacklisted including simple locking'''
    if config['filtering'] is False:
        return None, None

    testvalue = str(value)
    if not checkip:
        testvalue = regex.split('\s+', str(value))[-1].lower() # Get last value/parameter

    rvalue = testvalue[::-1]

    result = None
    blocktype = None
    hitdata = None
    fromcache = False
    parent_result = None

    #if value in check_cache:
    if rvalue in check_cache_trie:
        fromcache = True
        #result, hitdata = check_cache.get(value, None)
        result, blocktype, hitdata = check_cache_trie.get(rvalue, (None, None))

    elif not checkip:
        parent = check_cache_trie.longest_prefix(rvalue).key or None
        if parent:
            parent_result, parent_blocktype, parent_hitdata = check_cache_trie.get(parent, (None, None))
            if parent_result is True:
                if config['smartdoms'] and rvalue in bl_dom_trie:
                    logging.info('{0}-CHECK-RESULT [WHITELISTED/BLACKLISTED]: \"{1}\" -> \"{2}\" / \"{1}\"'.format(valuetype, testvalue, parent[::-1]))
                    parent_result = None

                if parent_result is True:
                    result = parent_result
                    blocktype = parent_blocktype
                    hitdata = parent[::-1]


    if result is None:
        count = 0
        while count < config['retry_count'] and testvalue in beingchecked:
            count += 1
            #logging.debug('{0}-BLACKLIST-SLEEP: {1} (#{2})'.format(valuetype, testvalue, count))
            time.sleep(config['retry_wait'])

        if count >= config['retry_count']:
            logging.error('{0}-BLACKLIST-FAIL: \"{1}\" -> \"{2}\" - Took to long to check'.format(valuetype, qname, testvalue))
            return None, None

        beingchecked.add(testvalue)

        result, blocktype, hitdata = check_blacklisted(qname, testvalue, valuetype, checkip)

        check_cache_trie[value[::-1]] = result, blocktype, hitdata

        prune = int(time.time()) % 60
        while prune in (0, 30) and len(check_cache_trie) > check_cache_size:
             first = list(check_cache_trie.keys())[0]
             try:
                  res, hit = check_cache_trie.pop(first)
             except:
                  pass

             logging.info('CHECK-CACHE: Pruned \"{0}\" -> \"{1}\" -> \"{2}\" ({3})'.format(first[::-1], res, hit, len(check_cache_trie)))

        beingchecked.discard(testvalue)


    if config['log_hits'] and result is not None:
        checklog = '\"{0}\"'.format(testvalue)
        if testvalue != hitdata:
            checklog = '{0} -> {1}:\"{2}\"'.format(checklog, blocktype, hitdata)

        if qname not in (testvalue, hitdata):
            checklog = '\"{0}\" -> {1}'.format(qname, checklog)
       
        if checkip:
            geodata = geo(testvalue)
            if hitdata != geodata:
                checklog = '{0} ({1})'.format(checklog, geodata)

        state = blacklisted_state.get(result, 'NOT-LISTED')

        if fromcache:
            state = 'CACHE-{0}'.format(state)

        if parent_result is not None:
            state = 'PARENT-{0}'.format(state)
     
        logging.info('{0}-CHECK-RESULT [{1}]: {2}'.format(valuetype, state, checklog))

    return result, hitdata


def check_blacklisted(qname, testvalue, valuetype, checkip):
    '''Check value is white/black-listed'''
    orgtestvalue = testvalue

    if config['blockip4'] and ((checkip is False and ip4arpa.search(testvalue)) or (checkip is True and is_ip4.search(testvalue))):
        if config['log_hits'] and config['log_verbose']:
            logging.warning('{0}-IPV4-HIT: \"{1}\" -> {2}'.format(valuetype, qname, testvalue))
        return True, 'BLOCK-IPV4', testvalue
    elif config['blockip6'] and ((checkip is False and ip6arpa.search(testvalue)) or (checkip is True and is_ip6.search(testvalue))):
        if config['log_hits'] and config['log_verbose']:
             logging.warning('{0}-IPV6-HIT: \"{1}\" -> {2}'.format(valuetype, qname, testvalue))
        return True, 'BLOCK-IPV6', testvalue

    # Check against domain
    if checkip is False and is_dom.search(testvalue):
        #logging.debug('CHECK-{0}: \"{1}\" is a DOMAIN'.format(valuetype, testvalue))
        #wcheck = check_dom(valuetype, testvalue, wl_dom, 'WHITELIST', False, False) # Whitelisted
        wcheck = check_dom_trie(valuetype, testvalue, wl_dom_trie, 'WHITELIST', False, False) # Whitelisted
        if wcheck:
            #if config['block_specific'] and wcheck != testvalue and testvalue in bl_dom:
            if config['block_specific'] and wcheck != testvalue and testvalue[::-1] in bl_dom_trie:
                if config['log_hits'] and config['log_verbose']:
                   if qname != testvalue:
                        logging.warning('{0}-SPECIFIC-NAME-DOM-HIT [BLACKLIST]: \"{1}\" -> \"{2}\" (Parent \"{3}\" is WHITELISTED)'.format(valuetype, qname, testvalue, wcheck))
                   else:
                       logging.warning('{0}-SPECIFIC-NAME-DOM-HIT [BLACKLIST]: \"{1}\" (Parent \"{2}\" is WHITELISTED)'.format(valuetype, testvalue, wcheck))
                return True, 'WHITE-DOM', wcheck

            #if config['smartdoms'] and check_dom_smart('WHITELIST', testvalue, bl_dom, 'BLACKLIST', True):
            if config['smartdoms']:
                #bcheck = check_dom_smart_trie('WHITELIST', testvalue, bl_dom_trie, 'BLACKLIST', True, wcheck)
                bcheck = check_dom_smart_trie('WHITELIST', testvalue, bl_dom_trie, 'BLACKLIST', True, False)
                if bcheck:
                    return True, 'BLACK-DOM', bcheck
            return False, 'WHITE-DOM', wcheck

        rcheck = check_rx(valuetype, orgtestvalue, wl_rx, wl_big_rx, 'WHITELIST')
        if rcheck:
            return False, 'WHITE-RX', rcheck

        #if config['check_ratio']:
        #    if check_ratio(valuetype, testvalue, wl_dom, 'WHITELIST'):
        #        return False

        if config['check_tld']:
            if not tld_rx.search(testvalue): # Invalid TLD
                if config['log_hits'] and config['log_verbose']:
                    logging.warning('{0}-NXTLD-HIT: {1}'.format(valuetype, testvalue))
                return True, 'NXTLD', '.{0}'.format(testvalue.strip('.').split('.')[-1])

        #if check_dom(valuetype, testvalue, bl_dom, 'BLACKLIST', False, config['smartdoms']): # Blacklisted
        bcheck = check_dom_trie(valuetype, testvalue, bl_dom_trie, 'BLACKLIST', False, config['smartdoms']) # Blacklisted
        if bcheck:
            #if config['smartdoms'] and check_dom_smart('BLACKLIST', testvalue, alias, 'ALIAS', True):
            if config['smartdoms']:
                acheck = check_dom_trie('BLACKLIST', testvalue, alias_trie, 'ALIAS', False, False)
                if acheck:
                    return False, 'ALIAS-DOM', acheck
            return True, 'BLACK-DOM', bcheck

        rcheck = check_rx(valuetype, orgtestvalue, bl_rx, bl_big_rx, 'BLACKLIST')
        if rcheck:
            return True, 'BLACK-RX', rcheck

        #if config['check_ratio']:
        #    if check_ratio(valuetype, testvalue, bl_dom, 'BLACKLIST'):
        #        return True

        # Check if Domain is a rev-arpa domain, if it is, check its IP value
        ip = False
        if ip4arpa.search(testvalue):
            ip = '.'.join(testvalue.strip('.').split('.')[0:4][::-1]) # IPv4
        elif ip6arpa.search(testvalue):
            ip = expand_ip(':'.join(filter(None, regex.split('(.{4,4})', ''.join(testvalue.strip('.').split('.')[0:32][::-1]))))) # IPv6

        if ip:
            #logging.debug('CHECK-{0}-ARPA-2-IP: {1} -> {2}'.format(valuetype, testvalue, ip))
            checkip = True
            testvalue = ip

    if checkip:
        ip4 = True
        if testvalue.find(':') > -1:
            ip4 = False

        # Check against IP4
        if ip4:
            #logging.debug('CHECK-{0}: {1} is an IPv4-Address'.format(valuetype, testvalue))
            # Check if IPv4 is whitelisted
            ipcheck = check_ip(qname, valuetype, testvalue, orgtestvalue, wl_ip4, 'WHITELIST')
            if ipcheck:
                return False, 'WHITE-IPV4', ipcheck

            else:
                # Check if IPv4 is blacklisted
                ipcheck = check_ip(qname, valuetype, testvalue, orgtestvalue, bl_ip4, 'BLACKLIST')
                if ipcheck:
                    #if rev_check(testvalue, wl_dom, 'WHITELIST'):
                    rcheck = rev_check_trie(testvalue, wl_dom_trie, 'WHITELIST')
                    if rcheck:
                        return False, 'WHITE-REV-DOM', rcheck
                    else:
                        return True, 'BLACK-IPV4', ipcheck


        # Check against IP6
        else:
            #logging.debug('CHECK-{0}: {1} is an IPv6-Address'.format(valuetype, testvalue))
            # Check if IPv6 is whitelisted
            ipcheck = check_ip(qname, valuetype, testvalue, orgtestvalue, wl_ip6, 'WHITELIST')
            if ipcheck:
                return False, 'WHITE-IPV6', ipcheck

            else:
                # Check if IPv6 is blacklisted
                ipcheck = check_ip(qname, valuetype, testvalue, orgtestvalue, bl_ip6, 'BLACKLIST')
                if ipcheck:
                    #if rev_check(testvalue, wl_dom, 'WHITELIST'):
                    rcheck = rev_check_trie(testvalue, wl_dom_trie, 'WHITELIST')
                    if rcheck:
                        return False, 'WHITE-REV-DOM', rcheck
                    else:
                        return True, 'BLACK-IPV6', ipcheck

        # Check against GEO
        gcheck = check_geo(qname, valuetype, testvalue, wl_geo, 'WHITELIST')
        if gcheck:
            return False, 'WHITE-GEO', gcheck

        gcheck = check_geo(qname, valuetype, testvalue, bl_geo, 'BLACKLIST')
        if gcheck:
            return True, 'BLACK-GEO', gcheck
  
    # Check against DNSWL/BL
    if dnsl_check(config['dnswl'], orgtestvalue, checkip):
        if config['log_hits']:
            logging.warning('{0}-WHITELIST-DNSL-HIT: \"{1}\"'.format(valuetype, testvalue))
        return False, 'WHITE-DNSL', orgtestvalue

    if dnsl_check(config['dnsbl'], orgtestvalue, checkip):
        if config['log_hits']:
            logging.warning('{0}-BLACKLIST-DNSL-HIT: \"{1}\"'.format(valuetype, testvalue))
        return True, 'BLACK-DNSL', orgtestvalue

    return None, None, None


def check_rx(valuetype, testvalue, rxlst, rxbiglst, tag):
    '''Match value against regex'''
    if config['use_regex']:
        #logging.debug('{0}-CHECK-RX: {1}'.format(valuetype, testvalue))

        if config['use_quick_regex']:
            match = rxbiglst.search(testvalue) or rxbiglst.search(testvalue.rstrip('.')) # Traling dot is optional when doing regex to make it easier
            if match:
                if config['log_hits']:
                    logging.warning('{0}-{1}-QUICK-RX-HIT: \"{2}\" matches \"{3}\"'.format(valuetype, tag, testvalue, match.group()))
                return match.group()

        else:
            for rx in rxlst:
                rgx = rxlst[rx]
                match = rgx.search(testvalue) or rgx.search(testvalue.rstrip('.'))
                if match:
                    if config['log_hits']:
                        logging.warning('{0}-{1}-RX-HIT: \"{2}\" matches \"{3}\" (Match: \"{4}\")'.format(valuetype, tag, testvalue, rx, match.group()))
                    return rx

    return False


def check_dom_fast(trielist, qname):
    return trielist.longest(qname[::-1]).key[::-1] or False
    #return trielist.shortest_prefix(qname[::-1]).key[::-1] or False


def check_dom_trie(valuetype, testvalue, trielist, listname, onlyparent, smart):
    match = trielist.longest_prefix(testvalue[::-1]).key
    #match = trielist.shortest_prefix(testvalue[::-1]).key or False
    if match:
        fqdn = match[::-1]

        if onlyparent and fqdn == testvalue:
            #check_cache[cachename] = False
            return False
        else:
            if config['log_hits'] and config['log_verbose'] and listname:
                dhlog = '\"{0}\"'.format(testvalue)
                if fqdn != testvalue:
                    dhlog = '{0} -> \"{1}\"'.format(dhlog, fqdn)

                logging.warning('{0}-TRIE-DOM-HIT [{1}]: {2}'.format(valuetype, listname, dhlog))
            #check_cache[cachename] = fqdn
            return fqdn

    if smart:
        return check_dom_smart_trie(valuetype, testvalue, trielist, listname, onlyparent, False)

    return False


def check_dom_smart_trie(valuetype, testvalue, trielist, listname, onlyparent, stripdom):
    # !!! FIX STRIPDOM !!!
    if stripdom and testvalue.endswith('.{0}'.format(stripdom)):
        valuetest = regex.sub('\.{0}$'.format(regex.escape(stripdom)), '.dummy', testvalue)
    else:
        valuetest = testvalue.rstrip('.')

    #suffix = ''
    while valuetest.count('.') > 1:
        valuetest = '.'.join(valuetest.split('.')[:-1])
        match = trielist.longest_prefix('{0}.'.format(valuetest)[::-1]).key or False
        #match = trielist.shortest_prefix('{0}.'.format(valuetest)[::-1]).key or False
        if match and match.count('.') > 1:
            fqdn = match[::-1]
            if config['log_hits'] and config['log_verbose'] and listname:
                logging.warning('{0}-TRIE-SMARTDOM-HIT [{1}]: \"{2}\" -> \"{3}\"'.format(valuetype, listname, testvalue, fqdn))
            return fqdn

    return False


def check_dom(valuetype, testvalue, domlist, listname, onlyparent, smart):
    '''Match domain against list, works for subdomains too'''
    #cachename = 'DOM#{0}#{1}#{2}'.format(listname or 'NONE', valuetype, testvalue)
    #if cachename in check_cache:
    #    return check_cache.get(cachename, False)

    if onlyparent is not True and testvalue in domlist:
        if config['log_hits'] and listname:
            logging.warning('{0}-DOM-HIT [{1}]: \"{2}\"'.format(valuetype, listname, testvalue))
        #check_cache[cachename] = testvalue
        return testvalue

    fqdn = check_dom_walk(valuetype, testvalue, domlist, listname, onlyparent)
    if fqdn:
        #check_cache[cachename] = fqdn
        return fqdn

    if smart:
        fqdn = check_dom_smart(valuetype, testvalue, domlist, listname, onlyparent)
        if fqdn:
            return fqdn

    #check_cache[cachename] = False
    return False


def check_dom_smart(valuetype, testvalue, domlist, listname, onlyparent):
    #cachename = 'DOM#{0}#{1}#{2}'.format(listname or 'NONE', valuetype, testvalue)
    #if cachename in check_cache:
    #    return check_cache.get(cachename, False)

    valuetest = testvalue.rstrip('.')
    while valuetest.count('.') > 1:
        valuetest = '.'.join(valuetest.split('.')[:-1])
        #logging.info('{0}-SMARTDOM: Checking {1}.'.format(listname, valuetest))
        fqdn = check_dom_walk(valuetype, '{0}.'.format(valuetest), domlist, False, False)
        if fqdn and fqdn.count('.') > 1:
            if config['log_hits'] and listname:
                logging.warning('{0}-SMARTDOM-HIT [{1}]: \"{2}\" -> \"{3}\"'.format(valuetype, listname, testvalue, fqdn))
            #check_cache[cachename] = fqdn
            return fqdn

    return False


def check_dom_walk(valuetype, testvalue, domlist, listname, onlyparent):
    fqdn = ''
    for label in filter(None, testvalue.strip('.').split('.')[::-1]):
        #fqdn = '{0}.{1}'.format(label, fqdn.lstrip('.'))
        fqdn = '{0}.{1}'.format(label, fqdn)
        #logging.debug('{0}-DOMWALK [{1}]: \"{2}\" -> \"{3}\"'.format(valuetype, listname, testvalue, fqdn))
        if onlyparent and fqdn == testvalue:
            return False

        if fqdn in domlist:
            if config['log_hits'] and listname:
                logging.warning('{0}-DOMWALK-HIT [{1}]: \"{2}\" -> \"{3}\"'.format(valuetype, listname, testvalue, fqdn))

            return fqdn

    return False


# !!! WORK-IN-PROGRESS !!!
#def check_ratio(valuetype, testvalue, domlist, listname):
#    for dom in domlist: # !!! SPEED THIS UP !!!
#    #for dom in [x for x in domlist if x.endswith(testvalue) or x.startswith(testvalue)]: # !!! SPEED THIS UP !!!
#        ratio = similar(dom, testvalue)
#        #logging.info('RATIO: {0} ~ {1} = {2}'.format(testvalue, dom, ratio))
#        if ratio > 90:
#            if config['log_hits'] and listname:
#                logging.warning('{0}-DOM-RATIO-HIT [{1}]: \"{2}\" ~ \"{3}\" (Ratio:{4})'.format(valuetype, listname, testvalue, dom, ratio))
#            return dom
#
#    return False


def check_ip(qname, valuetype, testvalue, orgtestvalue, iplist, listname):
    '''Check if IP is listed'''
    #logging.debug('{0}-CHECK-IP [{1}]: {2}'.format(valuetype, listname, testvalue))
    if testvalue in iplist:
        ip = str(iplist.get_key(testvalue))
        if config['log_hits'] and config['log_verbose'] and listname:
            logging.warning('{0}-IP-HIT [{1}]: {2} -> {3} -> {4} ({5})'.format(valuetype, listname, qname, orgtestvalue, ip, geo(ip)))
        return ip

    return False


def check_geo(qname, valuetype, testvalue, geolst, listname):
    #logging.debug('{0}-CHECK-GEO [{1}]: {2}'.format(valuetype, listname, testvalue))
    giploc = '?/?/?/?/{0}'.format(geo(testvalue))
    city, area, country, continent = tuple(giploc.split('/')[-4:])
    giploc = giploc.lstrip('?/')

    if giploc:
        # !!! Make nicer/quicker
        if continent in geolst or 'CONTINENT:{0}'.format(continent) in geolst:
            if config['log_hits'] and config['log_verbose'] and listname:
                logging.warning('{0}-GEO-CONTINENT-HIT [{1}]: {2} -> {3} -> {4} ({5})'.format(valuetype, listname, qname, testvalue, continent, giploc))
            return continent

        if country in geolst or 'COUNTRY:{0}'.format(country) in geolst:
            if config['log_hits'] and config['log_verbose'] and listname:
                logging.warning('{0}-GEO-COUNTRY-HIT [{1}]: {2} -> {3} -> {4} ({5})'.format(valuetype, listname, qname, testvalue, country, giploc))
            return country

        if area in geolst or 'AREA:{0}'.format(area) in geolst:
            if config['log_hits'] and config['log_verbose'] and listname:
                logging.warning('{0}-GEO-AREA-HIT [{1}]: {2} -> {3} -> {4} ({5})'.format(valuetype, listname, qname, testvalue, area, giploc))
            return area

        if city in geolst or 'CITY:{0}'.format(city) in geolst:
            if config['log_hits'] and config['log_verbose'] and listname:
                logging.warning('{0}-GEO-CITY-HIT [{1}]: {2} -> {3} -> {4} ({5})'.format(valuetype, listname, qname, testvalue, city, giploc))
            return city

        # Multiples
        #glist = [continent, country, area, city]
        glist = {'CONTINENT':continent, 'COUNTRY':country, 'AREA':area, 'CITY':city}
        gcheck = False
        for label in glist:
            value = glist[label]
            if value == '?':
                break

            if gcheck:
                gcheck = '{0}/{1}'.format(value, gcheck)
            else:
                gcheck = value

            #logging.info('GEO-DEBUG: {0} - {1} - {2}'.format(label, value, gcheck))
            if gcheck in geolst:
                if config['log_hits'] and config['log_verbose'] and listname:
                    logging.warning('{0}-GEO-HIT [{1}]: {2} -> {3} -> {4}'.format(valuetype, listname, qname, testvalue, gcheck))
                return gcheck
        
    return False


# !!! FIX - Better handling of quotas per dat for AbuseIPDB
def check_badip(cip):
    if not config['filtering'] or not is_ip.search(cip):
        return False

    cip = addzero(cip)

    #logging.info('BADIP: Checking {0}'.format(cip))

    count = 0
    while count < config['retry_count'] and cip in beingchecked:
        count += 1
        #logging.debug('BADIP-SLEEP: {0} (#{1})'.format(cip, count))
        time.sleep(config['retry_wait'])

    if count >= config['retry_count'] and cip in beingchecked:
        logging.error('BADIP-FAIL: {0} - Took to long to check'.format(cip))
        beingchecked.discard(cip)
        return False

    beingchecked.add(cip)

    if cip.find(':') > -1:
        wl_ip = wl_ip6
        bl_ip = bl_ip6
        private = private6
    else:
        wl_ip = wl_ip4
        bl_ip = bl_ip4
        private = private4

    if check_geo('IP', 'IP', cip, wl_geo, 'GEO-WHITELIST'):
        beingchecked.discard(cip)
        return False

    if check_geo('IP', 'IP', cip, bl_geo, 'GEO-BLACKLIST'):
        beingchecked.discard(cip)
        return True

    if (cip in private) or (cip in wl_ip):
        #if config['log_hits']:
            #logging.warning('IP-WHITELIST-HIT: {0} -> {1}'.format(cip, wl_ip.get_key(cip)))
        beingchecked.discard(cip)
        return False

    elif cip in bl_ip:
        if config['log_hits']:
            logging.warning('IP-BLACKLIST-HIT: {0} -> {1}'.format(cip, bl_ip.get_key(cip)))
        beingchecked.discard(cip)
        return True

    elif cip in private:
        return False

    elif config['abuseipdbkey']:
        score = False
        ipcheck = False

        #logging.debug('ABUSEIPDB-CHECK: {0}'.format(cip))

        url = 'https://api.abuseipdb.com/api/v2/check'
        querystring = {'ipAddress': cip, 'maxAgeInDays': '90'}
        headers = {'Accept': 'application/json', 'Key': config['abuseipdbkey']}

        count = 0
        while count < 3:
            count += 1

            try:
                #response = abuseipdb_session.get(url, timeout=5, headers=headers, params=querystring, allow_redirects=False, proxies=None, stream=True)
                response = requests.get(url, timeout=5, headers=headers, params=querystring, allow_redirects=False, proxies=None)
                if response.status_code == 200:
                    limit = int(response.headers['X-RateLimit-Limit'])
                    remain = int(response.headers['X-RateLimit-Remaining'])

                    logging.info('ABUSEIPDB-COUNT: {0}/{1}'.format(limit - remain, limit)) # Make debug

                    ipcheck = json.loads(response.text)
                    #logging.debug('ABUSEIPDB-JSON-DEBUG: {0}'.format(json.dumps(ipcheck, sort_keys=True, indent=4)))
                    break
                elif response.status_code == 429:
                    ipcheck = 'MAX'
                    logging.warning('ABUSEIPDB-USAGE: {0} - Max usage reached'.format(cip))
                    break
                else:
                    logging.error('ABUSEIPDB-GET-ERROR: {0} - {1} (#{2})'.format(cip, response.status_code, count))


            except BaseException as err:
                logging.error('ABUSEIPDB-ERROR: {0} - {1} (#{2})'.format(cip, err, count))

            time.sleep(config['retry_wait'])

        if ipcheck and ipcheck != 'MAX':
            score = ipcheck['data']['abuseConfidenceScore']
            logging.info('ABUSEIPDB-SCORE: {0} = {1}% ({2} - {3})'.format(cip, score, ipcheck['data']['countryCode'], ipcheck['data']['isp']))

            if score and score > 90:
                if config['log_hits']:
                    logging.warning('ABUSEIPDB-BLACKLIST-HIT: Score for Client {0} = {1}% ({2})'.format(cip, score, geo(cip)))
                bl_ip[cip] = True
                beingchecked.discard(cip)
                return True


    if dnsl_check(config['dnsbl'], cip, True):
        if config['log_hits']:
            logging.warning('ACL-DNSBL-BLACKLIST-HIT: {0}'.format(cip))
        bl_ip[cip] = True
        beingchecked.discard(cip)
        return True

    wl_ip[cip] = 'Auto-Whitelisted' # !!! Use something else, will work for now - Can be utilized/misused to auto-whitelist when flooding

    beingchecked.discard(cip)
    return False


def rev_check_trie(testvalue, trielist, tag):
    if config['check_iprev']:
        arpaip = rev_ip(testvalue, False)
        if arpaip:
            #logging.debug('IP-REV-{0}-LOOKUP: {1} = {2}'.format(tag, testvalue, arpaip))
            qid = random.randint(1025, 65535)
            rcode, response = dns_query(arpaip, 1, 12, qid, 'IP-REV', True, config['rc_ttl'])[0:2] # Check PTR
            if rcode == 0:
                for rrset in response:
                    for rr in rrset:
                        if hasattr(rr, 'target'):
                            target = str(rr.target)
                            wcheck = check_dom_trie('NAME', target, trielist, tag, False, False)
                            if wcheck:
                                if config['log_hits'] and config['log_verbose']:
                                    logging.warning('IP-REV-PTR-{0}-HIT: \"{1}\" -> \"{2}\" -> \"{3}\" -> \"{4}\"'.format(tag, testvalue, arpaip, target, wcheck))
                                return '{0} / {1}'.format(target, wcheck)

    return False


def rev_check(testvalue, domlist, tag):
    if config['check_iprev']:
        arpaip = rev_ip(testvalue, False)
        if arpaip:
            #logging.debug('IP-REV-{0}-LOOKUP: {1} = {2}'.format(tag, testvalue, arpaip))
            qid = random.randint(1025, 65535)
            rcode, response = dns_query(arpaip, 1, 12, qid, 'IP-REV', True, config['rc_ttl'])[0:2] # Check PTR
            if rcode == 0 and countrr(response) > 0:
                for rr in response:
                    target = regex.split('\s+', str(rr))[-1].lower()
                    if target and is_dom.search(target):
                        if check_dom('NAME', target, domlist, tag, False, False):
                            logging.warning('IP-REV-PTR-{0}-HIT: {1} = {2} = {3}'.format(tag, testvalue, arpaip, target))
                            return True

    return False


def rrrr(response):
    answer = response[1]
    if answer:
        new_answer = []
        for rrset in answer:
            newrrdata = rrset
            rdtypet = dns.rdatatype.to_text(rrset.rdtype)
            rrname = str(rrset.name)
            ttl = int(rrset.ttl)

            if rrset.rdtype in (1, 28) and len(rrset) > 1:
                #logging.debug('ROUNDROBIN-BEFORE: {0}/{1} = {2}'.format(rrname, rdtypet,', '.join(list(map(str, rrset)))))
                newrrdata = []
                if config['randomroundrobin']:
                    r = random.randint(1, len(rrset))
                else:
                    r = 1

                for rrd in list(map(str, rrset[r:] + rrset[:r])):
                    newrrdata.append(rrd)

                #logging.debug('ROUNDROBIN-AFTER: {0}/{1} = {2}'.format(rrname, rdtypet, ', '.join(newrrdata)))

            new_answer.append(dns.rrset.from_text_list(rrname, ttl, 'IN', rdtypet, newrrdata))
    else:
        return response

    return (response[0], new_answer, response[2], response[3], response[4])


def geonames(geoname):
    geol = list('////{0}'.format(geoname).split('/')[-4:])
    if geol[0]: geol[0] = 'CITY:{0}'.format(geol[0])
    if geol[1]: geol[1] = 'AREA:{0}'.format(geol[1])
    if geol[2]: geol[2] = 'COUNTRY:{0}'.format(geol[2])
    if geol[3]: geol[3] = 'CONTINENT:{0}'.format(geol[3])
    return list(filter(None, geol))

   
def geosteer(cip, qname, answer):
    if config['geo_steer'] and is_ip.search(cip) and answer:
        if cip.find(':') < 0 and cip in private4 and config['override_ecs_ip4']:
            logging.info('GEO-STEER: Private IP {0} -> {1}'.format(cip, config['override_ecs_ip4']))
            cip = config['override_ecs_ip4']
        elif cip.find(':') > -1 and cip in private6 and config['override_ecs_ip6']:
            logging.info('GEO-STEER: Private IP {0} -> {1}'.format(cip, config['override_ecs_ip6']))
            cip = config['override_ecs_ip6']

        geoinfo = geo(cip)
        steerlist = geonames(geoinfo)
        #if config['log_verbose']:
        #    logging.info('STEERLIST: {0} -> {1}'.format(cip, ', '.join(steerlist)))

        if steerlist:
            new_answer = []
            for rrset in answer:
                rrname = str(rrset.name)
                rdtypet = dns.rdatatype.to_text(rrset.rdtype)
                ttl = int(rrset.ttl)
                rrdatalist = list(map(str, rrset))
                newrrdata = []
                geodata = set()
                if rrset.rdtype in (1, 28) and len(rrdatalist) > 1:
                    #logging.info('GEO-STEER: Orginal order: {0}/{1} = {2}'.format(rrname, rdtypet, ', '.join(rrdatalist)))
                    for ip in rrdatalist:
                        #if config['log_verbose']:
                        #    logging.info('GEO-STEER-RR: {0}/{1} = {2} ({3})'.format(rrname, rdtypet, ip, geo(ip)))

                        geoname = check_geo(qname, 'IP', ip, steerlist, False)
                        if geoname:
                            if config['log_verbose']:
                                logging.info('GEO-STEER: Client {0} close to {1} ({2}) for {3}/{4}'.format(cip, ip, geoname, rrname, rdtypet))
                        #    newrrdata.insert(0, ip)
                            newrrdata.append(ip)
                            geodata.add(geoname)
                        #else:
                        #    newrrdata.append(ip)

                    #logging.info('GEO-STEER: New order: {0}/{1} = {2}'.format(rrname, rdtypet, ', '.join(newrrdata)))
                
                if newrrdata and geodata and len(newrrdata) < len(rrdatalist):
                    logging.info('GEO-STEERED: {0}/{1} from {2} to {3} answers (Client {4} ~ {5})'.format(rrname, rdtypet, len(rrdatalist), len(newrrdata), cip, ', '.join(geodata)))
                    rrdatalist = newrrdata

                new_answer.append(dns.rrset.from_text_list(rrname, ttl, 'IN', rdtypet, rrdatalist))

            if new_answer:
                return new_answer

    return answer


def collapse(name, rdtype, answer, qid):
    if answer:
        if config['collapse'] and answer[0].rdtype == 5 and rdtype != 5:
            #if answer[-1].rdtype in (1, 28): # CNAME and A/AAAA
            if answer[-1].rdtype == rdtype: # Needs to end in rdtype
                new_answer = []
                beforecount = 0
                aftercount = 0
                removed = 0
                newrrdata = []

                for rrset in answer:
                    ttl = int(rrset.ttl)
                    rrname = str(rrset.name)
                    beforecount += len(rrset)
                    #if rrset.rdtype in (1, 28): # A and AAAA
                    if rrset.rdtype == rdtype:
                        aftercount += len(rrset)
                        rrdata = list(map(str, rrset))

                        if rrdata:
                            newrrdata += rrdata
                            new_answer.append(dns.rrset.from_text_list(name, ttl, 'IN', dns.rdatatype.to_text(rrset.rdtype), rrdata))

                    elif config['log_collapse'] and config['log_verbose']:
                        for r in list(map(str, rrset)):
                            removed -= 1
                            logging.info('COLLAPSE [{0}]: Removed CNAME \"{1}\" -> \"{2}\" ({3})'.format(qid, rrname, r, removed))

                if new_answer:
                    if config['log_collapse']:
                        if config['log_verbose']:
                            logging.info('COLLAPSE [{0}]: Generated: \"{1}\" -> {2} ({3} RRs)'.format(qid, name, ', '.join(newrrdata), len(newrrdata)))
                        logging.info('COLLAPSE [{0}]: \"{1}\" went from {2} to {3} RRs ({4})'.format(qid, name, beforecount, aftercount, removed))

                    return new_answer
            else:
                if config['log_verbose']:
                    logging.warning('COLLAPSE [{0}]: \"{1}\" cannot be collapsed - no {2}'.format(qid, name, dns.rdatatype.to_text(rdtype)))
            
    return answer


# !!!! NEEDS WORK !!!!
def dnsl_check(dnsl, value, isip):
    if config['use_dnsl'] and config['nameservers'] and (not iparpa.search(value)):
        for service in dnsl:
            servicename, servicetype, domain = '{0}::'.format(service).lower().split(':')[0:3]
            if servicename and servicetype and domain and (not value.endswith('.' + domain)):
                qname = False
                tag = 'UNKNOWN'
                if isip and (servicetype == 'ip' or (servicetype == 'ip4' and is_ip4.search(value)) or (servicetype == 'ip6' and is_ip6.search(value))):
                    tag = 'IP'
                    iprev = rev_ip(value, False)
                    if iprev:
                        qname = regex.sub('\.(in-addr|ip6)\.arpa.', '.', iprev) + domain
                elif servicetype == 'dom' and (not isip):
                    tag = 'DOM'
                    qname = value + domain

                if qname:
                    servicename = servicename.upper()
                    cachename = '{0}/IN/A'.format(qname)
                    qid = random.randint(1025, 65535)
                    if config['log_requests']:
                        logging.info('DNSL-CHECK-{0} [{2}]: {3} ({4}) on {1}'.format(tag, servicename, qid, value, qname))
 
                    rcode, response = dns_query(qname, 1, 1, qid, 'DNSL', True, config['dnsl_ttl'])[0:2]

                    if rcode == 0 and countrr(response) > 0:
                        if config['log_responses']:
                            logging.info('DNSL-CHECK-{0}-RESPONSE [{2}] {3} = LISTED on {1}'.format(tag, servicename, qid, value))
                        return True

                    elif rcode == 3: # NXDOMAIN
                        if config['log_responses']:
                            logging.info('DNSL-CHECK-{0}-RESPONSE [{2}] {3} = NOT-LISTED on {1}'.format(tag, servicename, qid, value))

                    else:
                        logging.error('DNSL-CHECK-{0}-RESPONSE [{2}] {3} = ERROR - {4} - {5} using {1}'.format(tag, servicename, qid, value, rcode, response))
                        
    return False


def dns_query(name, rdclass, rdtype, qid, cip, unfilter, fttl):
    '''Do DNS Query and process'''
    # Get from cache
    qname = str(name)
    qrdtype = str(dns.rdatatype.to_text(rdtype))
    #cip = addzero(str(cip))

    cachename = '{0}/IN/{1}'.format(qname, qrdtype)

    rv = None
    returnstatus = 'OK'
    blacklistname = False

    ip6 = None
    if is_ip.search(cip):
        ip6 = False
        if cip.find(':') > -1:
            ip6 = True

        if config['use_ecs_ip']:
            if ip6:
                bits = config['cache_ip6_bits'] or 56
            else:
                bits = config['cache_ip4_bits'] or 24

            cache_ip = '{0}'.format(IP(cip).make_net(str(bits)).strNormal(0))
            cachename = '{0}/{1}'.format(cachename, cache_ip)

    else:
        unfilter = True

    if unfilter:
        cachename = '{0}/IN/{1}/{2}'.format(qname, qrdtype, cip)
        if ip6 is None:
            logging.info('INTERNAL-{0}-UNFILTER: {1}'.format(cip, cachename))

    logging.info('CACHE-NAME: {0} for {1}'.format(cachename, cip))

    if not unfilter:
        if qrdtype == 'ANY' and config['blockany']:
            logging.warning('BLOCK-ANY-HIT [{0}]: {1}'.format(qid, cachename))
            soa = dns.rrset.from_text(qname, config['blacklist_ttl'], 'IN', 6, 'blocked. any. {0} 60 60 60 60'.format(int(time.time())))
            return (dns.rcode.REFUSED, [], [soa], [])

        # Absolete, Experimental or not used
        # https://www.iana.org/assignments/dns-parameters/dns-parameters.xhtml
        if qrdtype in ('A6', 'AXFR', 'DLV', 'HINFO', 'IXFR', 'LOC', 'MAILA', 'MAILB', 'MB', 'MF', 'MG', 'MR', 'NONE', 'NULL', 'NXT', 'OPT', 'RP', 'SPF', 'WKS', 'X25'):
            logging.warning('RRTYPE-NOTIMP-HIT [{0}]: {1} -> {2}'.format(qid, qname, qrdtype))
            soa = dns.rrset.from_text(qname, config['blacklist_ttl'], 'IN', 6, 'blocked.{0}. notimp. {1} 60 60 60 60'.format(qrdtype, int(time.time())))
            return (dns.rcode.NOTIMP, [], [soa], [])

        if is_formerr('REQUEST', qname, qrdtype):
            #return (dns.rcode.SERVFAIL, [], [], [])
            soa = dns.rrset.from_text(qname, config['blacklist_ttl'], 'IN', 6, 'blocked. formerr. {0} 60 60 60 60'.format(int(time.time())))
            return (dns.rcode.FORMERR, [], [soa], [])

    if qname.endswith('.command.'):
        command = regex.sub('\.command\.$', '', qname).upper()
        if command and ((cip in command_acl4) or (cip in command_acl6)):
            subcommand = command.split('.')[0]
            if subcommand != command:
                command = command.split('.')[1]
            else:
                subcommand = 'NONE'

            logging.info('COMMAND-STARTED: {0} ({1})'.format(command, subcommand))
            if command == 'FLUSH':
                clear_caches()

            elif command == 'TOGGLE':
                if config['filtering'] is True:
                    config['filtering'] = False
                else:
                    config['filtering'] = True

                clear_caches()

            elif command == 'ON':
                config['filtering'] = True
                clear_caches()

            elif command == 'OFF':
                config['filtering'] = False
                clear_caches()

            elif command == 'FLUSH':
                clear_caches()

            elif command == 'STATS':
                hitlist = {}
                for entry in cache.entries():
                    hitlist[entry.name] = entry.hits

                count = 0
                for entry in sorted(hitlist, key=hitlist.get, reverse=True): #[0:50]
                    count += 1
                    logging.info('CACHE-STATS: #{0} {1} = {2} Cache-Hits'.format(count, entry, hitlist.get(entry, 0)))

            else:
                logging.error('COMMAND-UNKNOWN: {0}'.format(command))
                soa = dns.rrset.from_text(qname, 0, 'IN', 6, 'unknown.command. {0}. {1} 60 60 60 60'.format(command.lower(), int(time.time())))
                return (dns.rcode.NXDOMAIN, [], [soa], [])

        else:
            logging.error('COMMAND-REFUSED (ACL): {0} from {1}'.format(command, cip))
            soa = dns.rrset.from_text(qname, 0, 'IN', 6, 'refused.ip.command. {0}. {1} 60 60 60 60'.format(command.lower(), int(time.time())))
            return (dns.rcode.REFUSED, [], [soa], [])

        logging.info('COMMAND-FINISHED: {0}'.format(command))
        soa = dns.rrset.from_text(qname, 0, 'IN', 6, 'finished.command. {0}. {1} 60 60 60 60'.format(command.lower(), int(time.time())))
        return (dns.rcode.NOERROR, [], [soa], [])
 

    # Get from cache
    parentcount = -1
    lcachename = cachename.split('/')[0]
    rcachename = '/'.join(cachename.split('/')[1:])
    
    maxparentcount = lcachename.count('.') - 1
    first = True
    while parentcount < maxparentcount:
        if first:
            first = False
            gcachename = cachename
        else:
            parentcount += 1
            parentcachename = '.'.join(lcachename.split('.')[parentcount:])
            gcachename = '{0}/{1}'.format(parentcachename, rcachename)

        result = cache.get(gcachename, None)
        if result is not None:
            obj = cache.info(name=gcachename)
            left = int(obj.expires - time.time())
            #logging.info('CACHE-HITS: {0} = {1} hits'.format(cachename, obj.hits))
            if gcachename == cachename:
                result = update_ttls(qid, qname, result, left)
                if ['log_caching']:
                    log_helper(qname, qrdtype, result, 'RESPONSE-FROM-CACHE', qid, False)
                #return rrrr(result)
                return result

            elif config['parent_cache_hit']:
                if result[0] != 0: # Parent cache not NOERROR
                    newresult = update_ttls(qid, qname, (result[0], [], result[2], [], result[4]), left)
                    if config['log_caching'] and config['log_hits']:
                        logging.info('PARENT-CACHE-HIT [{0}]: {1} -> {2} -> {3} (TTL-LEFT:{4}) - {5}'.format(qid, cachename, gcachename, dns.rcode.to_text(newresult[0]), left, newresult[4]))
                        log_helper(qname, qrdtype, newresult, 'RESPONSE-FROM-PARENT-CACHE', qid, False)
                    #return rrrr(newresult)
                    return newresult

                elif config['redirect_ip'] and len(result[1]) > 0: # parent cache redirect ip
                    for rrset in result[1]:
                        if rrset.rdtype in (1, 28): # Only A and AAAA
                            for rr in rrset:   
                                if hasattr(rr, 'address'):
                                    target = str(rr.address)
                                    if target in config['redirect_ip']:
                                        result = update_ttls(qid, qname, result, left)
                                        if config['log_hits'] and config['log_caching']:
                                            logging.info('PARENT-CACHE-HIT [{0}]: {1} -> {2} -> {3} (TTL-LEFT:{4}) - {5}'.format(qid, cachename, gcachename, target, left, result[4]))
                                            log_helper(qname, qrdtype, result, 'RESPONSE-FROM-PARENT-CACHE', qid, False)
                                        #return rrrr(result)
                                        return result
            else: # No parent check
                break


    # Prematch forwarders/aliases to speed things up
    matcha = False
    matchb = False
    matchf = check_dom_trie('NAME', qname, forwarder_trie, 'FORWARDER', False, False)
    if matchf:
        if config['smartdoms']:
            #matchb = check_dom_smart_trie('FORWARDER-NAME', qname, bl_dom_trie, 'BLACKLIST', False, matchf)
            matchb = check_dom_smart_trie('FORWARDER-NAME', qname, bl_dom_trie, 'BLACKLIST', False, False)
            if matchb:
                if config['log_hits']:
                    logging.warning('FORWARDER-BLACKLIST-HIT: \"{0}\" -> \"{1}\" -> \"{2}\"'.format(qname, matchf, matchb))
                matchf = False

    if rv is None and config['filtering'] and config['filter_request'] and unfilter is False and (not matchf):
        matcha = check_dom_trie('NAME', qname, alias_trie, 'ALIAS', False, False)
        if not matcha:
            wmatch = None
            if matchb:
                wmatch = True
            else:
                wmatch, hitdata = is_blacklisted(qname, qname, 'NAME', False) # Due first, faster due to caching of previous results

            if wmatch is True:
                blacklistname = qname
                returnstatus = 'BLACKLISTED'
                rv = (config['blacklist_rcode'], [], [], [])

            elif wmatch is False:
                returnstatus = 'WHITELISTED'

            elif config['blockip4'] and (qrdtype == 'A' or qname.endswith('.in-addr.arpa.')):
                returnstatus = 'BLACKLISTED'
                if config['log_hits']:
                    logging.warning('REQUEST-IPV4-HIT [{0}]: {1}'.format(qid, cachename))
                rv = (config['blacklist_rcode'], [], [], [])

            elif config['blockip6'] and (qrdtype == 'AAAA' or qname.endswith('.ip6.arpa.')):
                returnstatus = 'BLACKLISTED'
                if config['log_hits']:
                     logging.warning('REQUEST-IPV6-HIT [{0}]: {1}'.format(qid, cachename))

                #rv = (dns.rcode.NOERROR, [], [], []) # Workaround for searchdomains
                rv = (config['blacklist_rcode'], [], [], [])

        if rv is None and (qrdtype in ('A', 'AAAA', 'CNAME')) and ((ip6 is False and cip in private4) or (ip6 is True and cip in private6)): # Only spoof answers for queries from private clients
            if matcha:
                #spoof = alias[match]
                spoof = alias_trie[matcha[::-1]]
                if spoof != qname:
                    count = 0
                    #while count < config['retry_count'] and (qname in beingspoofed or check_dom('NAME', qname, beingspoofed, 'SPOOFER-CHECKER', False, False)):
                    while count < config['retry_count'] and (qname in beingspoofed):
                        count += 1
                        #logging.debug('SPOOF-SLEEP: {0} (#{1})'.format(qname, count))
                        time.sleep(config['retry_wait'])

                    if count >= config['retry_count']:
                        logging.error('SPOOF-FAIL: {0} - Took to long to check'.format(qname))
                        rv = (dns.rcode.SERVFAIL, [], [], [])

                    else:
                        beingspoofed.add(qname)

                        if config['log_hits']:
                            logging.warning('SPOOFING-HIT [{0}]: \"{1}\" -> \"{2}\"'.format(qid, qname, ', '.join(spoof.split(','))))

                        if is_rc.search(spoof):
                            if spoof in ('NODATA', 'NOERROR'):
                                rv = (dns.rcode.NOERROR, [], [], [])
                            elif spoof == 'NXDOMAIN':
                                rv = (dns.rcode.NXDOMAIN, [], [], [])
                            elif spoof == 'REFUSED':
                                rv = (dns.rcode.REFUSED, [], [], [])
                            elif spoof == 'SERVFAIL':
                                rv = (dns.rcode.SERVFAIL, [], [], [])
                            elif spoof == 'RANDOM':
                                if qrdtype != 'CNAME':
                                    addrs = []
                                    for i in range(0, random.randint(0, 8)):
                                        if qrdtype == 'A':
                                            addrs.append(str(random.randint(0, 255)) + '.' + str(random.randint(0, 255)) + '.' + str(random.randint(0, 255)) + '.' + str(random.randint(0, 255)))
                                        elif qrdtype == 'AAAA':
                                            addrs.append(':'.join(filter(None, regex.split('(.{4,4})', ''.join([random.choice('0123456789abcdef') for _ in range(32)])))))

                                    if addrs:
                                        rv = (dns.rcode.NOERROR, [dns.rrset.from_text_list(qname, config['spoof_ttl'], 'IN', rdtype, addrs)], [], [])

                        elif is_dom.search(spoof):
                            rcode = False
                            qresponse = False
                            spoof = make_dom(spoof)
                            rcode, qresponse = dns_query(spoof, 1, rdtype, random.randint(1025, 65535), 'SPOOFER', False, False)[0:2]

                            if rcode == dns.rcode.NOERROR and qresponse:
                                qresponse.insert(0, dns.rrset.from_text(qname, config['spoof_ttl'], 'IN', 5, spoof)) # IN/CNAME
                                #qresponse = collapse(qname, rdtype, qresponse, qid)
                                rv = (dns.rcode.NOERROR, qresponse, [], [])
                                spoof = 'ALIAS'
                            elif rcode:
                                rv = (rcode, [], [], [])
                                spoof = 'ALIAS-' + dns.rcode.to_text(rcode) + '.' + spoof

                        else:
                            if qrdtype == 'A':
                                addrs = filter(is_ip4.search, spoof.split(','))
                                if addrs:
                                    rv = (dns.rcode.NOERROR, [dns.rrset.from_text_list(qname, config['spoof_ttl'], 'IN', 1, addrs)], [], []) # IN/A
                            elif qrdtype == 'AAAA':
                                addrs = filter(is_ip6.search, spoof.split(','))
                                if addrs:
                                    rv = (dns.rcode.NOERROR, [dns.rrset.from_text_list(qname, config['spoof_ttl'], 'IN', 28, addrs)], [], []) # IN/AAAA
                            spoof = 'REDIRECT' # Keep logging clean

                        if rv is not None:
                            returnstatus = 'SPOOFED'
                            soa = dns.rrset.from_text(matcha, config['spoof_ttl'], 'IN', 6, 'spoofed.{0} {1}.{2}. {3} 60 60 60 60'.format(qname, qrdtype.lower(), spoof.rstrip('.').lower(), int(time.time())))
                            rv = (rv[0], rv[1], [soa], rv[3])

                        else:
                            if config['log_requests']:
                                logging.info('SPOOFING [{0}]: NO spoof-results for \"{1}\"'.format(qid, qname))

                        beingspoofed.discard(qname)

                else:
                    logging.warning('NO-SPOOF [{0}]: Same or Sub-Domain for \"{1}\" -> \"{2}\"'.format(qid, qname, spoof))


    addrs = False
    if rv is None:
        fwdtag = None
        if matchf:
            fwdtag = 'SELECTIVE'
            #addrs = roundrobin(forwarder[matchf].split(','), False)
            addrs = roundrobin(forwarder_trie[matchf[::-1]].split(','), False)
            if cip in addrs:
                logging.error('FORWARD-LOOP [{0}]: \"{1}\" from {2} (forwarder for {3})'.format(qid, cachename, cip, matchf))
                return (dns.rcode.SERVFAIL, [], [], [])
            #forwarder[matchf]= ','.join(addrs) # Preserve roundrobin order
            forwarder_trie[matchf[::-1]]= ','.join(addrs) # Preserve roundrobin order

        else:
            fwdtag = 'DEFAULT'
            addrs = roundrobin(config['nameservers'], False)
            config['nameservers'] = addrs # Preserve roundrobin order

        result = False
        response = None

        #rttstart = time.time()
        response, _ = dox_request(qid, qname, rdtype, cachename, addrs, False, cip)
        #rresponse, _ = root_resolve(qname, rdtype)
        #logging.info('DEBUG: {0}'.format(rresponse))
        #rttend = time.time()
        #logging.info('RTT [{0}]: Resolving {1} took {2} msec'.format(qid, cachename, round((rttend - rttstart) * 1000)))

        if response is not None:
            rv = (response.rcode(), response.answer, response.authority, response.additional)
            rcode = str(dns.rcode.to_text(response.rcode()))

            if is_ip.search(cip) and config['log_server']:
                log_helper(qname, rdtype, (rcode, response.answer, response.authority, response.additional), 'RESPONSE-FROM-SERVER', qid, False)

            if rcode == 'NOERROR':
                seen = set()
                seen.add(str(qname)) # To skip first qname entry as already checked

                status = None

                if fwdtag == 'DEFAULT' and config['filtering'] and config['filter_response'] and unfilter is False:
                    if returnstatus != 'OK': # eg, not WHITELISTED
                        status = False
                    else:
                        sections = {'ANSWER':response.answer, 'AUTHORITY':response.authority, 'ADDITIONAL':response.additional }
                        for section in sections:
                            for rrset in sections.get(section, []):
                                rrdtype = dns.rdatatype.to_text(rrset.rdtype)
                                rrname = str(rrset.name)
                                if rrname not in seen:
                                    seen.add(rrname) # Unduplicate data/qname chain
                                    #logging.debug('RESPONSE-CHAIN-NAME-CHECK [{0}]: {1}'.format(qid, rrset.name))
                                    if is_formerr('CHAIN-NAME', rrname, rrdtype):
                                        status = True
                                        blacklistname = rrname
                                        break
                                    else:
                                        status, hitdata = is_blacklisted(qname, rrname, 'CHAIN-NAME', False)
                                        if status is not None:
                                            if status is True: # Blacklisted
                                               returnstatus = 'BLACKLISTED'
                                               blacklistname = rrname
                                               break
                                            else: # Whitelisted
                                               returnstatus = 'WHITELISTED'
                                               break

                                if rrdtype in ('A', 'AAAA', 'CNAME', 'MX', 'NS', 'PTR', 'SRV'):
                                    for rr in rrset.copy():
                                        if hasattr(rr, 'target'):
                                            target = str(rr.target)
                                        elif hasattr(rr, 'address'):
                                            target = str(rr.address)
                                        else:
                                            target = str(rr)

                                        #logging.info('RR [{0}]: {1}/{2}={3} ({4})'.format(qid, rrname, rrdtype, target, section))

                                        if target not in seen:
                                            seen.add(target)
                                            #logging.debug('RESPONSE-TARGET-CHECK [{0}]: {1}'.format(qid, target))

                                            if is_formerr('RESPONSE', target, rrdtype):
                                                status = True
                                                returnstatus = 'BLACKLISTED'
                                                blacklistname = target
                                                break
                                            elif rrdtype in ('A', 'AAAA') and (config['redirect_ip'] and target in config['redirect_ip']):
                                                logging.warning('REDIRECT-IP-HIT: {0} -> {1} ({2})'.format(rrname, target, section))
                                                status = False
                                                returnstatus = 'WHITELISTED'
                                                break
                                            else:
                                                if rrdtype in ('A', 'AAAA'):
                                                    status, hitdata = is_blacklisted(rrname, target, 'DATA', True)
                                                else:
                                                    if rrdtype == 'CNAME':
                                                        tag = 'CNAME-CLOAK'
                                                    else:
                                                        tag = '{0}-DATA'.format(rrdtype)

                                                    status, hitdata = is_blacklisted(rrname, target, tag, False)

                                                if status is not None:
                                                    if status is True: # Blacklisted
                                                        if config['remove_ip'] and rrdtype in ('A', 'AAAA'): # Remove IP from answer instead of blocking whole
                                                            rrset.remove(rr)
                                                            rrcount = len(rrset)
                                                            if config['log_verbose']:
                                                                rlog = '\"{0}\" -> \"{1}\" ({2} RRs left)'.format(rrname, hitdata, rrcount)
                                                                if qname != rrname:
                                                                    rlog = '\"{0}\" -> {1}'.format(qname, rlog)
                                                                logging.warning('REMOVED-IP: {0} from {1} ({2})'.format(target, rlog, section))

                                                            if rrcount == 0:
                                                                status = True
                                                                returnstatus = 'BLACKLISTED'
                                                                blacklistname = rrname
                                                                break

                                                            status = None

                                                        else:
                                                            if rrdtype not in ('A', 'AAAA'):
                                                                if config['log_hits'] and config['log_verbose']:
                                                                    cloaklog='\"{0}\" -> \"{1}\"'.format(rrname, target)
                                                                    if target != hitdata:
                                                                        cloaklog='{0} -> \"{1}\"'.format(cloaklog, hitdata)
                                                                    if qname != rrname:
                                                                         cloaklog = '\"{0}\" -> {1}'.format(qname, cloaklog)
                                                                    logging.warning('{0}-BLACKLIST-CLOAK-HIT: {1} ({2})'.format(rrdtype, cloaklog, section))

                                                            status = True
                                                            returnstatus = 'BLACKLISTED'
                                                            blacklistname = target
                                                            break

                                                    else: # Whitelisted
                                                        status = False
                                                        returnstatus = 'WHITELISTED'
                                                        break

                                else:
                                    status = None

                                if status is not None or returnstatus != 'OK': # White or Blacklisted
                                    break


                if status is True:
                    returnstatus = 'BLACKLISTED'
                    rv = (config['blacklist_rcode'], [], [], [])
                else:
                    before = len(response.answer)
                    response.answer = collapse(qname, rdtype, response.answer, qid)

                    if len(response.answer) != before:
                         returnstatus = '{0}-COLLAPSED'.format(returnstatus)

                    rv = (response.rcode(), response.answer, response.authority, response.additional)


        else:
            logging.error('REQUEST-ERROR: {0} = SERVFAIL - Empty Response'.format(cachename))
            rv = (dns.rcode.SERVFAIL, [], [], [])
    
    if rv:
        num = countrr(rv[1])
        rcode = rv[0]

        if not is_ip.search(cip):
            log_helper(qname, qrdtype, rv, 'RESPONSE-FROM-{0}'.format(cip), qid, False)

        if config['fix_noerror'] and rcode == dns.rcode.NOERROR and num < 1:
            logging.warning('FIX-NOERROR-ZERO-ANSWER [{0}]: {1} NOERROR -> NXDOMAIN'.format(qid, cachename))
            rcode = dns.rcode.NXDOMAIN
            rv = (dns.rcode.NXDOMAIN, [], rv[2], [])

        if config['fix_nxdomain'] and rcode == dns.rcode.NXDOMAIN:
            logging.warning('FIX-NXDOMAIN [{0}]: {1} NXDOMAIN -> NOERROR/NODATA'.format(qid, cachename))
            rcode = dns.rcode.NOERROR
            rv = (dns.rcode.NOERROR, [], rv[2], [])

        #if config['fix_cname'] and rcode == dns.rcode.NOERROR and num > 0 and rv[1][0].rdtype == 5 and (rv[1][-1].rdtype not in (1, 28)): #CNAME and no Address A/AAAA
        if config['fix_cname'] and rcode == dns.rcode.NOERROR and num > 0 and rv[1][0].rdtype == 5 and rdtype != 5 and rv[1][-1].rdtype != rdtype: #CNAME not ending in requested type
            returnstatus = '{0}-NOADDRESS'.format(returnstatus)

            newrdtype = False
            ip = False

            if config['fix_cname_redirect'] and config['redirect_ip']:
                ttl = rv[1][0].ttl
                if rdtype in (1, 5): # A or CNAME
                    newrdtype = 1
                    ip = list(filter(is_ip4.search, config['redirect_ip']))

                elif rdtype in (5, 28): # CNAME or AAAA
                    newrdtype = 28
                    ip = list(filter(is_ip6.search, config['redirect_ip']))

            if newrdtype and ip:
                logging.warning('FIX-CNAME-NO-{0} [{1}]: {2} -> {3}'.format(qrdtype, qid, cachename, '.'.join(ip)))
                rv = (dns.rcode.NOERROR, [dns.rrset.from_text_list(qname, ttl, 'IN', newrdtype, ip)], rv[2], [])
            else:
                logging.warning('FIX-CNAME-NO-{0} [{1}]: {2} -> NXDOMAIN'.format(qrdtype, qid, cachename))
                rv = (dns.rcode.NXDOMAIN, [], rv[2], [])

        num = countrr(rv[1])
        rcode = rv[0]


        # TTL
        ttl = False

        # Get SOA TTL if avaible
        ttl = get_soa_ttl(rv[2])

        # Determine TTL
        if blacklistname:
            ttl = config['blacklist_ttl']

        elif rcode in (dns.rcode.FORMERR, dns.rcode.NOTIMP, dns.rcode.SERVFAIL) and not ttl:
            ttl = config['rc_error_ttl']

        elif rcode in (dns.rcode.NXDOMAIN, dns.rcode.REFUSED) and not ttl:
            ttl = config['rc_ttl']

        else:
            if rv[1]: # Get ttl from answer section
                ttl = rv[1][-1].ttl
            elif ttl:
                logging.info('AUTH-TTL [{0}]: {1} = {2}'.format(qid, cachename, ttl))
                ttl = norm_ttl(qid, qname, ttl, config['rc_ttl'], config['max_ttl'])
            else:
                ttl = config['min_ttl']


        if returnstatus.find('BLACKLISTED') > -1:
            tag = 'blocked'
            if qname.strip('.') != blacklistname.strip('.'):
                 tag = '{0}.cloaked'.format(tag)
                 
            soa = dns.rrset.from_text(qname, ttl, 'IN', 6, '{0}.{1} {2}.{3}. {4} 60 60 60 60'.format(tag, qname, qrdtype.lower(), blacklistname.strip('.'), int(time.time())))

            newrv = False
            if rdtype in (1, 5) and config['redirect_ip']: # A or CNAME
                ip4 = list(filter(is_ip4.search, config['redirect_ip']))
                if ip4:
                    newrv = (dns.rcode.NOERROR, [dns.rrset.from_text_list(qname, ttl, 'IN', 1, ip4)], [soa], [])

            elif rdtype in (5, 28) and config['redirect_ip']: # CNAME or AAAA
                ip6 = list(filter(is_ip6.search, config['redirect_ip']))
                if ip6:
                    newrv = (dns.rcode.NOERROR, [dns.rrset.from_text_list(qname, ttl, 'IN', 28, ip6)], [soa], [])

            elif rdtype == 16: # TXT
                newrv = (dns.rcode.NOERROR, [dns.rrset.from_text(qname, ttl, 'IN', 16, 'Blacklisted!')], [soa], [])

            if newrv:
                rv = newrv
            else:
                rv = (config['blacklist_rcode'], [], [soa], [])


        if ttl and ttl > 0:
            rcode = rv[0]

            # All TTLs the same
            if rcode == dns.rcode.NOERROR and returnstatus.find('BLACKLISTED') < 0:
                ttl = norm_ttl(qid, qname, ttl, config['min_ttl'], config['max_ttl'])

            # Equalize TTLs
            rv = update_ttls(qid, qname, rv, ttl)

            # Geo-Steer
            rv = (rv[0], geosteer(cip, qname, rv[1]), rv[2], rv[3], returnstatus)

            # Cache it
            if config['log_caching']:
                log_helper(qname, rdtype, (rv[0], rv[1], rv[2], rv[3], returnstatus), 'RESPONSE-TO-CACHE', qid, False)
            cache.add(obj=CachedObject(name=cachename, obj=rv + (returnstatus,), ttl=ttl))

    else:
        rv = (dns.rcode.SERVFAIL, [], [], [])

    return (rv[0], rv[1], rv[2], rv[3], returnstatus)


def countrv(rv):
    if rv:
        count = 0
        for x in (1, 2, 3):
            if rv[x]:
                count += countrr(rv[x])

        return count

    return 0


def get_soa_ttl(rv):
    if rv:
        for rr in rv:
            if rr.rdtype == 6:
                return rr.ttl or False

    return False


def norm_ttl(qid, qname, ttl, minttl, maxttl):
    orgttl = ttl
    ttl = max(minttl, ttl)
    ttl = min(ttl, maxttl)
    if ttl != orgttl:
        logging.info('TTL [{0}]: Forced from {1} to {2} for {3}'.format(qid, orgttl, ttl, qname))
    return ttl


def update_ttls(qid, qname, result, ttl):
    for rrset in result[1]:
        rrset.ttl = ttl
    for rrset in result[2]:
        rrset.ttl = ttl
    for rrset in result[3]:
        rrset.ttl = ttl

    return result


# !!!! NEEDS WORK - TEST !!!!
def root_resolve(qname, qtype):
    if config['rootservers']:
        logging.info('ROOT-RESOLVE: {0}/{1}'.format(qname, qtype))
        nsaddr = config['rootservers']
        qname = '{0}.'.format(qname.strip('.'))
        rqname = ''
        for label in filter(None, qname.strip('.').split('.')[::-1]):
            rqname = '{0}.{1}'.format(label, rqname)
            logging.info('ROOT-RESOLVE: {0} - Query for {1} to {2}'.format(qname, rqname, ', '.join(nsaddr)))
            message = dns.message.make_query(encode_0x20(rqname), qtype)
            if type == dns.rdatatype.ANY:
                message.flags |= dns.flags.AD
                message.find_rrset(message.additional, dns.name.root, 65535, dns.rdatatype.OPT, create=True, force_unique=True)

            response = False
            try:
                response = dns.query.udp(message, nsaddr[0], timeout=5, port=53)

            except BaseException as err:
                logging.error('QUERY-ERROR: Query for {0}/IN/{1} to {2} - {3}'.format(qname, dns.rdatatype.to_text(qtype), ', '.join(nsaddr), err))

            if response:
                if response.rcode() == dns.rcode.NOERROR:
                    if response.answer:
                        return response, response.rcode
                    elif response.authority:
                        addr = False
                        if response.additional:
                            addr = []
                            for rrset in response.additional:
                                if str(rrset.name) == rqname and rrset.rdtype in (1, 28): # Get A/AAAA
                                   addr +=list(map(str, rrset))

                        if not addr:
                            # Fetch A/AAAA for NS and stick into nsaddr
                            ns = []
                            for rrset in response.authority:
                                if str(rrset.name) == rqname and rrset.rdtype == 2: # Get NS
                                   ns +=list(map(str, rrset))

                            if ns:
                                addr = []
                                for nsname in ns:
                                   for rrtype in (1, 28):
                                       logging.info('ROOT-RESOLVE: Query for {0} to {1}'.format(nsname, ', '.join(nsaddr)))
                                       message = dns.message.make_query(encode_0x20(nsname), rrtype) # Get address

                                       response = False
                                       try:
                                           response = dns.query.udp(message, nsaddr[0], timeout=5, port=53) # Use NSADDR standing

                                       except BaseException as err:
                                           logging.error('QUERY-ERROR: Query for {0}/IN/{1} to {2} - {3}'.format(nsname, dns.rdatatype.to_text(rrtype), ', '.join(nsaddr), err))

                                       if response:
                                           if response.rcode() == dns.rcode.NOERROR:
                                               for rrset in response.answer:
                                                   if str(rrset.name) == nsname and rrset.rdtype in (1, 28): # Get A/AAAA
                                                       addr +=list(map(str, rrset))

                        if addr:
                            nsaddr = addr
                            if labelcount > 0:
                                labelcount -= 1

                            else:
                                break # No answer
                        else:
                            break # No referal from additional

                    else:
                        break # No referal from authoritative

                else:
                    break # No referal

            else:
                break

    return None, dns.rcode.SERVFAIL


# !!!! WORK IN PROGRESS
# Code based and adapted on: https://www.bortzmeyer.org/hackathon-ietf-101.html
def dox_request(qid, qname, rdtype, cachename, urls, rfc8484, cip):
    global requests_session

    icip = cip
    ip6 = False
    if not is_ip.search(cip):
        icip = False
    elif cip.find(':') > -1:
        ip6 = True

    message = dns.message.make_query(encode_0x20(qname), rdtype)

    # Fixup for ANY
    # https://stackoverflow.com/questions/17681230/how-make-dns-queries-in-dns-python-as-dig-with-additional-records-section
    if rdtype == dns.rdatatype.ANY:
        message.flags |= dns.flags.AD
        message.find_rrset(message.additional, dns.name.root, 65535, dns.rdatatype.OPT, create=True, force_unique=True)
        #message.find_rrset(message.additional, dns.name.root, 4096, dns.rdatatype.OPT, create=True, force_unique=True)

    if config['add_ecs_ip'] and icip:
        ccip = cip
        bits = 0
        if ip6 or config['force6']:
            if config['override_ecs_ip6'] and is_ip6.search(config['override_ecs_ip6']):
                ccip = config['override_ecs_ip6']
            bits = config['ecs_privacy6'] or 48

        else:
            if config['override_ecs_ip4'] and is_ip4.search(config['override_ecs_ip4']):
                ccip = config['override_ecs_ip4']
            bits = config['ecs_privacy4'] or 24

        if config['log_ecs'] and ccip != cip:
            logging.info('EDNS-CLIENT-SUBNET-OVERRIDE [{0}]: {1} -> {2} ({3})'.format(qid, cip, ccip, geo(ccip)))

        ocip = IP(ccip).make_net(str(bits)).strNormal(0) # Convert to network with no mask

        if config['log_ecs']:
            if bits in (32, 128):
                logging.info('EDNS-CLIENT-SUBNET-ADD [{0}]: {1}/{2}'.format(qid, ocip, bits))
            else:
                logging.info('EDNS-CLIENT-SUBNET-PRIVACY [{0}]: {1} -> {2}/{3}'.format(qid, ccip, ocip, bits))

        cso = clientsubnetoption.ClientSubnetOption(ocip, bits)
        message.use_edns(edns=True, ednsflags=0, payload=1220, request_payload=None, options=[cso])
    else:
        message.use_edns(edns=False, ednsflags=0, payload=1220, request_payload=None, options=None)

    af = None
    aftag = 'AUTO-IPv4/6'
    if config['force4']:
        af = 2
        aftag = 'IPv4'
    elif config['force6']:
        af = 10
        aftag = 'IPv6'
    elif config['smartip']:
        if icip:
            if ip6:
                af = 10
                aftag = 'IPv6'
            else:
                af = 2
                aftag = 'IPv4'

        else:
            if rdtype == dns.rdatatype.A or ip4arpa.search(qname):
                af = 2
                aftag = 'IPv4'
            elif rdtype == dns.rdatatype.AAAA or ip6arpa.search(qname):
                af = 10
                aftag = 'IPv6'

    retries = 0
    starttime = int(time.time())
    while retries < 3 and (int(time.time()) - starttime < 10):
        for url in filter(None, urls):
            if url:
                #logging.info('DOX-URL: {0}/{1} -> {2}'.format(qname, dns.rdatatype.to_text(rdtype), url))

                fastretry = False
                retries += 1

                # DOH
                if url.startswith('https://'):
                    hostname = url.split('/')[2]
                    path = '/'.join(url.split('/')[3:])
                    port = 443
                    if hostname.find('@') > -1:
                        port = int(hostname.split('@')[1])
                        hostname = hostname.split('@')[0]
                    
                    if config['nextdns'] and config['nextdns_id']:
                        url += '/{0}-{1}'.format(regex.sub('\s+', '%20', config['nextdns_id']), regex.sub('[\.\:]+', '-', cip))

                    ips = False
                    if af is not None:
                        cached = cache.get('{0}/{1}/GETADDRINFO'.format(hostname, port))
                        if cached:
                            if af == 2:
                                ips = list(filter(is_ip4.search, list((map(lambda x: x[4][0], cached)))))
                            elif af == 10:
                                ips = list(filter(is_ip6.search, list((map(lambda x: x[4][0], cached)))))

                    if not ips:
                        ips = [None]
         
                    for ip in ips:
                        if ip and ip.find(':') > -1:
                            ip = '[{0}]'.format(ip)

                        dnsurl = 'https://{0}/{1}'.format(hostname, path)

                        if config['log_forwards']:
                            logging.info('DOH-QUERY [#{0}]: Query for {1}/IN/{2} to https://{3}@{4}/{5} (BOOTSTRAP-{6}: {7})'.format(retries, qname, dns.rdatatype.to_text(rdtype), hostname, port, path, aftag, ip))

                        response = False
                        try:
                            response = dns.query.https(message, dnsurl, post=config['doh_post'], port=int(port), timeout=5, session=requests_session, bootstrap_address=str(ip))

                        except BaseException as err:
                            logging.error('DOH-ERROR: Query for {0}/IN/{1} to {2} - {3}'.format(qname, dns.rdatatype.to_text(rdtype), url, err))
                            if af is not None:
                                af = None
                                fastretry = True

                        if response:
                            return response, response.rcode()

                #elif url.startswith('https://'):
                #    message.id = 0 # DoH requests this
                #    rcode = 500

                #    if rfc8484 and (not config['nextdns']): # Use GET
                #        if config['log_forwards']:
                #            logging.info('DOH-QUERY-GET [#{0}]: Query for {1}/IN/{2} to {3}'.format(retries, qname, dns.rdatatype.to_text(rdtype), url))

                #        headers = {'User-Agent': config['useragent'], 'Accept': 'application/dns-message', 'Content-type': 'application/dns-message'}
                #        dns_req = base64.urlsafe_b64encode(message.to_wire()).decode('UTF8').rstrip('=')
                #        fullurl = '{0}?ct&dns={1}'.format(url, dns_req)

                #        try:
                #            r = requests_session.get(fullurl, timeout=5, headers=headers, allow_redirects=False, proxies=None, stream=True)
                #            if r:
                #                rcode = r.status_code
                #        except BaseException as err:
                #            logging.error('DOH-ERROR-GET: Query for {0}/IN/{1} to {2} - {3}'.format(qname, dns.rdatatype.to_text(rdtype), url, err))

                #    else: # Use POST (Prefered)

                #        if config['log_forwards']:
                #            logging.info('DOH-QUERY-POST [#{0}]: Query for {1}/IN/{2} to {3}'.format(retries, qname, dns.rdatatype.to_text(rdtype), url))

                #        headers = {'User-Agent': config['useragent'], 'Accept': 'application/dns-udpwireformat', 'Content-type': 'application/dns-udpwireformat'}

                #        try:
                #            r = requests.post(url, data=message.to_wire(), timeout=5, headers=headers, allow_redirects=False, proxies=None, stream=True)
                #            if r:
                #                rcode = r.status_code
                #        except BaseException as err:
                #            logging.error('DOH-ERROR-POST: Query for {0}/IN/{1} to {2} - {3}'.format(qname, dns.rdatatype.to_text(rdtype), url, err))


                #    if rcode == 500:
                #        logging.warning('DOH-INFO: Re-initiating session')
                #        requests_session.close()
                #        time.sleep(config['retry_wait'])
                #        requests_session = requests.Session()
                #        requests_session.mount('https://', HTTP20Adapter())

                #    elif rcode == 200:
                #        #body = answerbuffer.getvalue() # Pycurl
                #        body = r.content
                #        if body:
                #            response = dns.message.from_wire(body)
                #            if response:
                #                if response.rcode() == dns.rcode.NOERROR:
                #                    return response, dns.rcode.NOERROR
                #                else:
                #                    return None, response.rcode()

                #        return None, dns.rcode.NXDOMAIN

                #    elif rcode in (401, 403):
                #        return None, dns.rcode.REFUSED

                #    else:
                #        return None, dns.rcode.SERVFAIL

                # TLS
                elif url.startswith('tls://'): # Port 853
                    servername, port = '{0}{1}'.format(regex.sub('^' + regex.escape('tls://'), '', url), '@853').split('@')[0:2]
                    if servername and port:
                        ips = False
                        if af is not None:
                            cached = cache.get('{0}/{1}/GETADDRINFO'.format(servername, port))
                            if cached:
                                if af == 2:
                                    ips = list(filter(is_ip4.search, list((map(lambda x: x[4][0], cached)))))
                                elif af == 10:
                                    ips = list(filter(is_ip6.search, list((map(lambda x: x[4][0], cached)))))

                        if ips:
                            for addr in ips:
                                if config['log_forwards']:
                                    logging.info('DOT-QUERY [#{0}]: Query for {1}/IN/{2} to {3}@{4} ({5})'.format(retries, qname, dns.rdatatype.to_text(rdtype), servername, port, addr))

                                    response = False
                                    try:
                                        response = dns.query.tls(message, addr, timeout=5, port=int(port), server_hostname=servername)

                                    except BaseException as err:
                                        logging.error('DOT-QUERY-ERROR: Query for {0}/IN/{1} to {2} - {3}'.format(qname, dns.rdatatype.to_text(rdtype), url, err))

                                    if response:
                                        return response, response.rcode()
                        else:
                            fastretry = True

                # DNS
                else:
                    addr = regex.sub('^' + regex.escape('dns://'), '', url)
                    addr, port = '{0}{1}'.format(addr, '@53').split('@')[0:2]
                    if is_ip.search(addr):
                        if addr and (af is None or ((af == 2 and is_ip4.search(addr)) or (af == 10 and is_ip6.search(addr)))):
                            if config['log_forwards']:
                                logging.info('DNS-QUERY [#{0}]: Query for {1}/IN/{2} to {3}@{4}'.format(retries, qname, dns.rdatatype.to_text(rdtype), addr, port))

                            response = False
                            try:
                                #response = dns.query.udp(message, addr, timeout=5, port=int(port), af=af)
                                response = dns.query.udp(message, addr, timeout=5, port=int(port))

                            except BaseException as err:
                                logging.error('DNS-QUERY-ERROR: Query for {0}/IN/{1} to {2} - {3}'.format(qname, dns.rdatatype.to_text(rdtype), url, err))

                            if response:
                                return response, response.rcode()
                        else:
                            fastretry = True

                if fastretry:
                    retries -= 1
                else:
                    time.sleep(config['retry_wait'])

    if int(time.time()) - starttime >= 10:
        logging.error('DNS-QUERY-TIMEOUT: Query for {0}/IN/{1} to {2} - Query took more then 10 secs'.format(qname, dns.rdatatype.to_text(rdtype), url))

    return None, dns.rcode.SERVFAIL


def clear_caches():
    cache.clear()
    unfilter_cache.clear()
    #check_cache.clear()
    geo_cache.clear()
    gc.collect() # Collect garbage
    return True


def countrr(rrsets):
    num = 0
    for rrset in rrsets:
        num += len(rrset)

    return num


def log_helper(qname, qrdtype, result, tag, qid, cip):
    rcode = result[0]
    if isinstance(rcode, int):
        rcode = dns.rcode.to_text(rcode)

    if isinstance(qrdtype, int):
        qrdtype = dns.rdatatype.to_text(qrdtype)

    if config['log_responses']:
        if rcode == 'NOERROR':
            log_response('{0}-ANSWER'.format(tag), qid, result[1])

        if config['log_verbose']:
            log_response('{0}-AUTHORITY'.format(tag), qid, result[2])
            log_response('{0}-ADDITIONAL'.format(tag), qid, result[3])

    if len(result) > 4:
        rcode = '{0}-{1}'.format(rcode, result[4])

    ttl = 0
    if result[1]:
        ttl = result[1][-1].ttl
    else:
        ttl = get_soa_ttl(result[2]) or 0
 
    #rlog = '{0} [{1}]: {2}/IN/{3} {4} = {5} (ANS: {6}, AUT: {7}, ADD: {8} RRs)'.format(tag, qid, qname, qrdtype, ttl, rcode, len(result[1]), len(result[2]), len(result[3]))
    rlog = '{0} [{1}]: {2}/IN/{3} {4} = {5} ({6} RRs)'.format(tag, qid, qname, qrdtype, ttl, rcode, countrv(result))
    if cip:
        rlog = '{0} to {1}'.format(rlog, cip)

    logging.info(rlog)

    return True


def log_response(tag, qid, answer):
    if answer:
        total = len(answer)
        count = 0
        for rrset in answer:
            count += 1
            rrname = str(rrset.name)
            ttl = int(rrset.ttl)
            rrtype = dns.rdatatype.to_text(rrset.rdtype)
            rrdata = list(map(str, rrset))
            if rrtype == 'AAAA':
                rrdata = list(map(compress_ip, rrdata))

            logging.info('{0} [{1}] RRSET {2} of {3}: {4} {5} IN {6} {7}'.format(tag, qid, count, total, rrname, ttl, rrtype, ', '.join(rrdata)))

    return


def make_our_response(query):
    '''Create Response'''
    response = dns.message.Message(query.id)
    response.flags = dns.flags.QR | dns.flags.RA | (query.flags & dns.flags.RD)
    response.set_opcode(query.opcode())
    response.question = list(query.question)
    return response


def geo(client_ip):
    if config['geodb']:
        cip = expand_ip(client_ip).split('/')[0]

        ip6 = False
        if cip.find(':') > -1:
            ip6 = True

        response = geo_cache.get(cip, None)
        if response:
            return response

        response = '?/?/?/?'

        if config['geodb'] and is_ip.search(cip):
            if cip in ('0.0.0.0', '0000:0000:0000:0000:0000:0000:0000:0000'):
                response = '?/?/?/NULL'

            elif cip in ('127.0.0.1', '0000:0000:0000:0000:0000:0000:0000:0001'):
                response = '?/?/?/LOCALHOST'

            elif (ip6 is False and cip in private4) or (ip6 is True and cip in private6):
                response = '?/?/?/PRIVATE'

            else:
                try:
                    gip = geoip.city(cip)
                    if gip:
                        #logging.info('GEOIP-DEBUG: {0} = G-ID:{1}/{2}/{3}/{4}'.format(cip, gip.city.geoname_id or 0, gip.subdivisions.most_specific.geoname_id or 0, gip.country.geoname_id or 0, gip.continent.geoname_id or 0))
                        #logging.info('GEOIP-DEBUG: {0} = G-NAME:{1}/{2}/{3}/{4}'.format(cip, gip.city.name or '?', gip.subdivisions.most_specific.name or '?', gip.country.name or '?', gip.continent.name or '?'))
                        response = regex.sub('[^a-zA-Z0-9\/\?]+', '', '{0}/{1}/{2}/{3}'.format(gip.city.name or '?', gip.subdivisions.most_specific.name or '?', gip.country.name or '?', gip.continent.name or '?')).upper()
                except:
                    pass

        if response == '?/?/?/?':
            response = 'UNKNOWN'
        else:
            response = response.lstrip('?/')

        geo_cache[cip] = response
        return response

    return ''


def handle_query(raw_data, client_ip):
    '''Handle Query'''
    try:
        query = dns.message.from_wire(raw_data)
    except dns.exception.DNSException as e:
        logging.error('REQUEST-ERROR: Query from {0} - {1}'.format(client_ip, e))
        return

    cip = addzero(str(client_ip))
    name = str(query.question[0].name).lower()
    rdclass = query.question[0].rdclass
    rdclasst = dns.rdataclass.to_text(rdclass)
    rdtype = query.question[0].rdtype
    rdtypet = dns.rdatatype.to_text(rdtype)
    queryname = '{0}/{1}/{2}'.format(name, rdclasst, rdtypet)
    bname = '{0}/{1}/*'.format(name, rdclasst)
    fromtrie = False

    # Need IPy.IP for octal conversion to real IP
    #if hasattr(query, 'options'):
    if config['use_ecs_ip'] and hasattr(query, 'options'):
        for opt in query.options:
            if isinstance(opt, clientsubnetoption.ClientSubnetOption):
                if hasattr(opt, 'ip') and hasattr(opt, 'mask'):
                    ipaddr = IP(opt.ip).strNormal(0)
                    if opt.mask in (None, 0, 32, 128):
                        if config['log_ecs'] and config['log_verbose']:
                            logging.info('EDNS-CLIENT-SUBNET [{0}]: Client {1} -> {2} ({3}) for {4}/{5}'.format(query.id, client_ip, ipaddr, geo(ipaddr), name, rdtypet))
                        cip = str(ipaddr)

                    elif config['log_ecs'] and config['log_verbose']:
                        logging.info('EDNS-CLIENT-SUBNET [{0}]: Client {1} provides subnet {2}/{3} for {4}/{5}'.format(query.id, client_ip, ipaddr, opt.mask, name, rdtypet))

                    break

    #logging.debug('GEO-IP: {0} - {1}'.format(client_ip, geo(client_ip)))

    if config['block_clients'] and check_badip(cip):
        logging.warning('DROP-CLIENT: {0} requesting {1}/{2}/{3} from {4}'.format(compress_ip(cip), name, rdtypet, rdclasst, geo(cip)))
        return None # DROP


    count = 0
    while count < config['retry_count'] and bname in beingchecked:
        count += 1
        #logging.debug('QUERY-SLEEP [{0}]: {1} ({2}) from {3} (#{4})'.format(query.id, queryname, bname, cip, count))
        time.sleep(config['retry_wait'])

    if count >= config['retry_count']:
        logging.error('REQUEST-SERVFAIL [{0}]: Query \"{1}\" took to long!'.format(query.id, queryname, len(query.question)))
        servfail = True

    #beingchecked.add(queryname)
    beingchecked.add(bname)

    if config['log_requests']:
        logging.info('REQUEST [{0}]: {1} from {2}'.format(query.id, queryname, cip))

    servfail = False

    if query.opcode() != 0: # Must be a query
        logging.error('REQUEST-SERVFAIL [{0}]: Query-OpCode for \"{1}\" NOT QUERY ({2})!'.format(query.id, queryname, query.opcode))
        servfail = True

    elif rdclass != 1:
        logging.error('REQUEST-SERVFAIL [{0}]: Query \"{1}\" not \"IN\" class!'.format(query.id, queryname))
        servfail = True

    elif len(query.question) != 1:
        logging.error('REQUEST-SERVFAIL [{0}]: Query \"{1}\" not 1 question ({2})!'.format(query.id, queryname, len(query.question)))
        servfail = True

    if servfail:
        result = (dns.rcode.SERVFAIL, [], [], [])

    if config['rrtype_allow'] and (rdtypet not in config['rrtype_allow']):
        logging.warning('BLOCK-RRTYPE-HIT [{0}]: {1} - \"{2}\" Not Allowed (Not: {3})'.format(query.id, queryname, rdtypet, ', '.join(config['rrtype_allow'])))
        result = (dns.rcode.NOERROR, [], [], [])
   
    else:
        #logging.debug('REQUEST-FLAGS-FROM-CLIENT [{0}]: {1}'.format(query.id, dns.flags.to_text(query.flags)))

        unfilter = False

        #if config['unfilter'] and (check_dom('NAME', name, forwarder, 'FORWARDER', False, False) is False):
        if config['unfilter'] and (check_dom_trie('NAME', name, forwarder_trie, 'FORWARDER', False, False) is False):
            if cip in unfilter_cache or name in unfilter_cache:
                unfilter = True

            elif (cip in ul_ip4 or cip in ul_ip6):
                unfilter = True
                if config['log_unfilter']:
                    logging.info('UNFILTER-IP [{0}]: {1}'.format(query.id, cip))
                unfilter_cache.add(obj=CachedObject(name=cip, obj=True, ttl=604800)) # 7 days

            else:
                #match = check_dom('NAME', name, ul_dom, 'UNFILTER', False, False)
                match = check_dom_trie('NAME', name, ul_dom_trie, 'UNFILTER', False, False)
                if match:
                    unfilter = True
                    if config['log_unfilter']:
                        unfilter_cache.add(obj=CachedObject(name=name, obj=True, ttl=config['unfilter_ttl']))
                    logging.info('UNFILTER-NAME [{0}]: From {1} for {2} ({3})'.format(query.id, cip, queryname, match))


        # Make query
        #result = False
        #triekey = '{0}.{1}'.format(name[::-1], rdtypet)
        #if triekey in big_trie:
        #    rcode, expire, rrdata, status = big_trie.get(triekey)
        #    if expire > time.time():
        #        fromtrie = True
        #        ttl = int(expire - time.time())
        #        logging.info('BIG-TRIE: Retrieved {0}/{1} -> {2} (TTL: {3})'.format(name, rdtypet, ', '.join(rrdata) or str(dns.rcode.to_text(rcode)), ttl))
        #        soa = []
        #        if rcode in (dns.rcode.NXDOMAIN, dns.rcode.REFUSED, dns.rcode.NOTIMP, dns.rcode.NOTAUTH, dns.rcode.NOTZONE):
        #            striekey = '{0}.SOA'.format(name[::-1])
        #            if striekey in big_trie:
        #                srcode, sexpire, srrdata, sstatus = big_trie.get(striekey)
        #                sttl = int(expire - time.time())
        #                logging.info('BIG-TRIE: Retrieved {0}/{1} -> {2} (TTL: {3})'.format(name, 'SOA', ', '.join(srrdata) or str(dns.rcode.to_text(srcode)), sttl))
        #                soa = [dns.rrset.from_text_list(name, sttl, 'IN', 'SOA', srrdata)]
        #            else:
        #                serial = int(time.time())
        #                logging.info('BIG-TRIE: Generated {0}/SOA -> {1}. {2}. {3}. 60 60 60 60 (TTL: {4})'.format(name, dns.rcode.to_text(rcode), rdtypet, serial, ttl))
        #                soa = [dns.rrset.from_text(name, ttl, 'IN', 'SOA', '{0}. {1}. {2} 60 60 60 60'.format(dns.rcode.to_text(rcode), rdtypet, serial))]

        #        result = (rcode, [dns.rrset.from_text_list(name, ttl, 'IN', rdtypet, rrdata)], soa, [], status)

        #    else:
        #        rcode, expire, rrdata, status = big_trie.pop(triekey)
        #        logging.info('BIG-TRIE: Pruned {0}/{1} -> {2} (Expired)'.format(name, rdtypet, ', '.join(rrdata) or str(dns.rcode.to_text(rcode))))

        #if result is False:

        result = dns_query(name, rdclass, rdtype, query.id, cip, unfilter, False)

    status = 'NORMAL'
    if len(result) > 4:
        status = result[4]
    else:
        result = (result[0], result[1], result[2], result[3], status)

    #if fromtrie is False:
    #    if result[0] != 0: # or (result[0] == 0 and len(result[1]) < 1):
    #        triekey = '{0}.{1}'.format(name[::-1], rdtypet)
    #        logging.info('BIG-TRIE: Stored {0}/{1} -> {2} (TTL: {3})'.format(name, rdtypet, str(dns.rcode.to_text(result[0])), config['rc_ttl']))
    #        # !!!! TODO: Take SOA TTL if availble !!!!
    #        big_trie[triekey] = result[0], int(time.time() + config['rc_ttl']), [], status
    #        # !!!! Reinstate SOA, quickfix for now
    #        soa = [dns.rrset.from_text(name, config['rc_ttl'], 'IN', 'SOA', '{0}. {1}. {2} 60 60 60 60'.format(dns.rcode.to_text(result[0]), rdtypet, int(time.time())))]
    #        result = (result[0], result[1], soa, [], result[4])

    #    for rrset in result[1] + result[2] + result[3]:
    #        ttl = rrset.ttl
    #        expire = int(time.time() + ttl)
    #        rrname = str(rrset.name)
    #        rrdtype = dns.rdatatype.to_text(rrset.rdtype)
    #        rrdata = []
    #        for rr in rrset:
    #            if hasattr(rr, 'target'):
    #                target = str(rr.target)
    #            elif hasattr(rr, 'address'):
    #                target = str(rr.address)
    #            else:
    #                target = str(rr)
 
    #            rrdata.append(target)

    #        triekey = '{0}.{1}'.format(rrname[::-1], rrdtype)
    #        logging.info('BIG-TRIE: Stored {0}/{1} -> {2} (TTL: {3})'.format(rrname, rrdtype, ', '.join(rrdata) or str(dns.rcode.to_text(result[0])), ttl))
    #        big_trie[triekey] = result[0], expire, rrdata, status


    #    if len(big_trie) > big_trie_size:
    #        for key in big_trie.copy():
    #            rcode, expire, rrdata, status = big_trie.get(key)
    #            if expire < time.time():
    #                btname = '.'.join(key.split('.')[:-1])[::-1]
    #                bttype = key.split('.')[-1]
    #                rcode, expire, rrdata, status = big_trie.pop(key)
    #                logging.info('BIG-TRIE: Pruned {0}/{1} -> {2} (Expired)'.format(btname, bttype, ', '.join(rrdata) or str(dns.rcode.to_text(rcode))))
                

    #    while len(big_trie) > big_trie_size:
    #        first = sorted(big_trie.items(), key=lambda x: x[1][1])[0][0]
    #        if first in big_trie:
    #            btname = '.'.join(first.split('.')[:-1])[::-1]
    #            bttype = first.split('.')[-1]
    #            try:
    #                rcode, expire, rrdata, status = big_trie.pop(first)
    #                ttl = int(expire - time.time())
    #                logging.info('BIG-TRIE: Pruned {0}/{1} -> {2} ({3}) - CACHE-FULL'.format(btname, bttype, ', '.join(rrdata) or str(dns.rcode.to_text(rcode)), ttl))
    #            except:
    #                pass

    if config['min_resp']:
        if result[0] == 0:
            if result[1]:
                result = (result[0], result[1], [], [])
            else:
                result = (result[0], [], result[2], [])
        else:
            result = (result[0], [], result[2], [])

    response = make_our_response(query)
    response.set_rcode(result[0]) or dns.rcode.SERVFAIL
    response.answer = result[1] or []
    response.authority = result[2] or []
    response.additional = result[3] or []

    #logging.debug('RESPONSE-FLAGS-TO-CLIENT [{0}]: {1}'.format(query.id, dns.flags.to_text(response.flags)))

    log_helper(name, rdtypet, (result[0], result[1], result[2], result[3], status), 'RESPONSE-TO-CLIENT', query.id, cip)

    beingchecked.discard(bname)

    return response


class UDPHandler(socketserver.BaseRequestHandler):
    '''UDP Handler'''
    def handle(self):
        raw_data, socket = self.request
        response = handle_query(raw_data, self.client_address[0])

        if not response:
            return

        try:
            raw_response = response.to_wire()
        except BaseException as err:
            #logging.debug('RESPONSE-ERROR-DEBUG: {0}'.format(response))
            logging.error('SOCKET-RESPONSE-TO-WIRE ERROR: {0}'.format(err))
            return

        if len(raw_response) <= 512:
            try:
                socket.sendto(raw_response, self.client_address)
            except BaseException as err:
                logging.error('SOCKET-SENDTO ERROR: {0}'.format(err))
                pass

        else:
            response.flags |= dns.flags.TC
            try:
                socket.sendto(response.to_wire()[:512], self.client_address)
            except BaseException as err:
                logging.error('SOCKET-SENDTO ERROR: {0}'.format(err))
                pass


class TCPHandler(socketserver.BaseRequestHandler):
    '''TCP Handler'''
    def handle(self):
        socket = self.request

        try:
            query_length_bytes = socket.recv(2)
            query_length = struct.unpack('!H', query_length_bytes)
            raw_data = socket.recv(query_length[0])
            response = handle_query(raw_data, self.client_address[0])

            if response is not None:
                raw_response = response.to_wire()
                response_length_bytes = struct.pack('!H', len(raw_response))
                socket.send(response_length_bytes + raw_response)
        except (struct.error, OSError):
            pass
        finally:
            socket.close()


class ThreadedUDPServer4(socketserver.ThreadingMixIn, socketserver.UDPServer):
    '''UDP Thread'''
    allow_reuse_address = True
    address_family = socket.AF_INET
    socket_type = socket.SOCK_DGRAM


class ThreadedTCPServer4(socketserver.ThreadingMixIn, socketserver.TCPServer):
    '''TCP Thread'''
    allow_reuse_address = True
    address_family = socket.AF_INET
    socket_type = socket.SOCK_STREAM


class ThreadedUDPServer6(socketserver.ThreadingMixIn, socketserver.UDPServer):
    '''UDP Thread'''
    allow_reuse_address = True
    address_family = socket.AF_INET6
    socket_type = socket.SOCK_DGRAM


class ThreadedTCPServer6(socketserver.ThreadingMixIn, socketserver.TCPServer):
    '''TCP Thread'''
    allow_reuse_address = True
    address_family = socket.AF_INET6
    socket_type = socket.SOCK_STREAM


def run_server():
    '''Run DNS Server'''
    ### !!! TO DO: Make multi-addres/port threads (ip-format <ip>[@port] e.g. 10.1.2.3@53).
    ### !!! FIX: Use combined IPv4/IPv6 handler detecting address-family so can listen on same ports/etc:
    ###    af = dns.inet.af_for_address(ipaddr)
    ###    https://gitlab.labs.nic.cz/knot/respdiff/blob/master/respdiff/sendrecv.py#L198

    ### TLS: https://stackoverflow.com/questions/46964122/how-to-create-a-tlslite-ng-server-with-tls-1-3-support-only

    #global requests_session

    dnsport = int(config['port'])

    logging.info('SERVER: DeugNietS Starting on port {0}'.format(dnsport))

    udp_server4 = ThreadedUDPServer4(('127.0.0.1', dnsport), UDPHandler)
    udp_server6 = ThreadedUDPServer6(('::1', dnsport), UDPHandler)
    udp_server_thread4 = threading.Thread(target=udp_server4.serve_forever)
    udp_server_thread6 = threading.Thread(target=udp_server6.serve_forever)

    tcp_server4 = ThreadedTCPServer4(('127.0.0.1', dnsport), TCPHandler)
    tcp_server6 = ThreadedTCPServer6(('::1', dnsport), TCPHandler)
    tcp_server_thread4 = threading.Thread(target=tcp_server4.serve_forever)
    tcp_server_thread6 = threading.Thread(target=tcp_server6.serve_forever)

    newnameservers = []

    # NextDNS Get best route/servers
    if config['nextdns']:
        url = 'https://router.nextdns.io'

        url += '?stack=dual'
        if config['nextdns_hpm']:
            url += '&hardened_privacy=1'

        rcode = 500
        headers = {'User-Agent': config['useragent']}
        try:
            #logging.info('NEXTDNS-FETCH: {0}'.format(url))
            r = requests.get(url, timeout=5, headers=headers, allow_redirects=False, proxies=None)
            if r:
                rcode = r.status_code
        except BaseException as err:
            logging.error('NEXTDNS-ERROR-GET-SERVERS: {0} - {1}'.format(url, err))

        if rcode == 200:
            config['doh_post'] = True
            config['roundrobin'] = False
            config['ecs_privacy4'] = 32
            config['ecs_privacy6'] = 128

            body = json.loads(r.text)
            if body:
                for server in range(0, len(body)):
                    dnshost = body[server]['hostname']
                    dnsurl = 'https://{0}'.format(dnshost)
                    dnsips = body[server]['ips']
        
                    if config['nextdns_config']:
                        dnsurl += '/{0}'.format(config['nextdns_config'])

                        #if config['nextdns_id']:
                        #    dnsurl += '/{0}'.format(regex.sub('\s+', '%20', config['nextdns_id']))

                    newnameservers.append(dnsurl)

                    getaddrinfo = []
                    for ip in dnsips:
                        tag = False
                        if ip.find(':') > -1:
                            tag = 'IPV6'
                            wl_ip6[ip] = 'NEXTDNS-Server'
                        else:
                            tag = 'IPV4'
                            wl_ip4[ip] = 'NEXTDNS-Server'

                        if config['block_clients'] and check_badip(cip):
                            logging.warning('NEXTDNS-SERVER-DISCARDED: {0} ({1})'.format(dnsurl, geo(ip)))
                            getaddrinfo = []
                            newnameservers.remove(dnsurl)
                            break

                        else:
                            if tag == 'IPV6':
                                getaddrinfo.append((10, 1, 6, '', (ip, 443, 0, 0)))
                            else:
                                getaddrinfo.append((2, 1, 6, '', (ip, 443)))

                            logging.info('NEXTDNS-{0}-SERVER-ADDED: {1} = {2} ({3})'.format(tag, dnsurl, ip, geo(ip)))

                    if getaddrinfo:
                        cachednshost = '{0}/443/GETADDRINFO'.format(dnshost)
                        cache.add(obj=CachedObject(name=cachednshost, obj=getaddrinfo, ttl=604800)) # 7 Days

            else:
                logging.error('NEXTDNS-ERROR-GET-SERVERS: {0} - Empty Response'.format(url))

        else:
            logging.error('NEXTDNS-ERROR-GET-SERVERS: {0} - RCODE={1}'.format(url, rcode))


    else:
        # !!! TODO: Define bootstrap servers to use to resolve below
        # !!! TODO: Make it possible to use @<portnum>
        for dnsserver in config['nameservers']:
            newentry = False
            hostname = dnsserver
            ips = False

            proto = hostname.split(':')[0].lower()
            if proto not in ('dns', 'https', 'tls'):
                proto = 'dns'
                hostname = 'dns://{0}'.format(hostname)

            if hostname.find('#') > -1:
                ips = regex.split('\s*,\s*', regex.split('\s*#\s*', hostname)[1])
                hostname = regex.split('\s*#\s*', hostname)[0]

            path = ''
            if len(hostname.split('/')) > 3:
                path = '/'.join(hostname.split('/')[3:])

            hostname = hostname.split('/')[2]

            port = int('{0}@0'.format(hostname).split('@')[1])
            hostname = hostname.split('@')[0]
            
            #if hostname.find('.opendns.com'):
            #    config['force4'] = True
            #    config['force6'] = False

            dox = proto.upper()
            aport = port or 53
            if dox == 'HTTPS':
                aport = port or 443
            elif dox == 'TLS':
                aport = port or 853

            # !!! Fix # addresses add
            if dox != 'DNS':
                if ips:
                    getaddrinfo = []
                    for ip in ips:
                        tag = False
                        if ip.find(':') > -1:
                            tag = 'IPV6'
                            wl_ip6[ip] = '{0}-Server'.format(dox)
                        else:
                            tag = 'IPV4'
                            wl_ip4[ip] = '{0}-Server'.format(dox)

                        if config['block_clients'] and check_badip(ip):
                            logging.warning('{0}-SERVER-DISCARDED: {1} = BOOTSTRAP:{2} ({3})'.format(dox, hostname, ip, geo(ip)))

                        else:
                            if tag == 'IPV6':
                                getaddrinfo.append((10, 1, 6, '', (ip, aport, 0, 0)))
                            else:
                                getaddrinfo.append((2, 1, 6, '', (ip, aport)))

                            logging.info('{0}-{1}-SERVER-ADDED: {2} = BOOTSTRAP:{3} ({4})'.format(dox, tag, hostname, ip, geo(ip)))

                    if getaddrinfo:
                        #logging.info('PRE-CACHE: {0}://{1}@{2} = {3}'.format(dox, hostname, aport, ', '.join(ips)))
                        cachednshost = '{0}/{1}/GETADDRINFO'.format(hostname, aport)
                        cache.add(obj=CachedObject(name=cachednshost, obj=getaddrinfo, ttl=604800)) # 7 Days

                else:
                    ips = list(map(lambda x: x[4][0], socket.getaddrinfo('{0}.'.format(hostname.rstrip('.')), aport, type=socket.SOCK_STREAM))) # Pre-cache

                newentry = '{0}://{1}@{2}'.format(dox.lower(), hostname, aport, path)
            else:
                newentry = 'dns://{0}@{1}'.format(hostname, aport)
                 
            if newentry:
                if path:
                    newentry = '{0}/{1}'.format(newentry, path)
                logging.info('{0}-NAME-SERVER: {1}'.format(dox, newentry, ','.join(ips) or '-'))
                newnameservers.append(newentry.lower())

    if newnameservers:
        config['nameservers'] = newnameservers


    logging.info('SERVER: DeugNietS Started - Accepting DNS requests on port {0}'.format(dnsport))

    try:
        #for thread in [udp_server_thread4, tcp_server_thread4, udp_server_thread6, tcp_server_thread6]:
        for thread in [udp_server_thread4, udp_server_thread6]:
            thread.start()

        #for thread in [udp_server_thread4, tcp_server_thread4, udp_server_thread6, tcp_server_thread6]:
        for thread in [udp_server_thread4, udp_server_thread6]:
            thread.join()

    except (KeyboardInterrupt, SystemExit):
        pass

    finally:
        #for server in [udp_server4, tcp_server4, udp_server6, tcp_server6]:
        for server in [udp_server4, udp_server6]:
            server.shutdown()
            server.server_close()

    return

if __name__ == '__main__':
    '''Main Beef'''
    logging.info('==============================')
    logging.info('SERVER: DeugNietS Starting ...')

    # Default Settings
    config = {}

    # Port to listen on
    config['port'] = 53

    # Nameservers to forward to
    config['nameservers'] = ['8.8.8.8', '8.8.4.4', '2001:4860:4860::8888', '2001:4860:4860::8844']

    # Root-servers
    # https://www.internic.net/domain/named.root
    config['rootservers'] = ['198.41.0.4', '2001:503:ba3e::2:30', '199.9.14.201', '2001:500:200::b', '192.33.4.12', '2001:500:2::c', '199.7.91.13', '2001:500:2d::d', '192.203.230.10', '2001:500:a8::e', '192.5.5.241', '2001:500:2f::f', '192.112.36.4', '2001:500:12::d0d', '198.97.190.53', '2001:500:1::53', '192.36.148.17 2001:7fe::53', '192.58.128.30', '2001:503:c27::2:30', '193.0.14.129', '2001:7fd::1', '199.7.83.42', '2001:500:9f::42', '202.12.27.33', '2001:dc3::35']

    # Use DoH POST instead of GET (Recommended: POST)
    config['doh_post'] = True

    # AbuseIPDB
    config['abuseipdbkey'] = False

    # GeoIP DB
    #config['geodb'] = '/usr/share/GeoIP/GeoLite2-City.mmdb'
    config['geodb'] = False

    # Cache Settings
    config['blacklist_ttl'] = 3600
    config['rc_ttl'] = 120
    config['rc_error_ttl'] = 30
    #config['min_ttl'] = 30
    config['min_ttl'] = 2400 # https://blog.apnic.net/2019/11/12/stop-using-ridiculously-low-dns-ttls/
    config['max_ttl'] = 86400
    config['spoof_ttl'] = 3600
    config['ttl_strategy'] = 'minimum' # average/minimum/maximum

    # Use EDNS CLIENT SUBNET (ECS) IP as client IP (only when /32 or /128)
    config['use_ecs_ip'] = True
    config['add_ecs_ip'] = True
    config['ecs_privacy4'] = 24 # ECS Privacy for IPv4 - Only show the /24
    config['ecs_privacy6'] = 48 # ECS Privacy for IPv6 - Only use the /48
    config['override_ecs_ip4'] = False
    config['override_ecs_ip6'] = False

    # Cache-subnet params
    config['cache_ip4_bits'] = 24
    config['cache_ip6_bits'] = 56

    # Random RoundRobin
    config['roundrobin'] = True
    config['randomroundrobin'] = False

    # CNAME Collapse
    config['collapse'] = True

    # Minimal Responses
    config['min_resp'] = True

    # Parent hit
    config['parent_cache_hit'] = False

    # Block IP related answers
    config['blockip4'] = False
    config['blockip6'] = True
    config['blockany'] = True
    config['blockroot'] = True
    config['smartip'] = True
    config['force4'] = False
    config['force6'] = False
    config['ignoreip'] = False
    config['blockweird'] = True
    config['check_iprev'] = False
    config['remove_ip'] = True
    config['block_specific'] = True # Block specific domains even when TLD is whitelisted
    config['block_clients'] = False

    # 0x20 encoding
    config['0x20'] = False

    # Lists
    config['whitelist'] = ['white.list']
    config['blacklist'] = ['black.list']
    config['private_addrs'] = []
    config['optimize'] = True
    config['optimize_mode'] = 1 # 0 = None, 1 = Light/Undup, 2 = Full

    # Logging
    config['log_requests'] = True
    config['log_responses'] = False
    config['log_server'] = False
    config['log_caching'] = False
    config['log_hits'] = True
    config['log_forwards'] = True
    config['log_collapse'] = False
    config['log_verbose'] = False
    config['log_ecs'] = False
    config['log_unfilter'] = False

    # Return codes
    config['blacklist_rcode'] = 'REFUSED'
    #config['blacklist_rcode'] = 'NOERROR' # Less retries/noise from DNS clients when asnwering NOERROR (NODATA)
    config['tld_rcode'] = 'NXDOMAIN'

    # Redirect
    config['redirect_ip'] = ['0.0.0.0', '::']

    # DNS BL/WL
    config['use_dnsl'] = False
    config['dnsbl'] = ['BLOCKLIST.DE:ip:de.bl.blocklist.de.', 'SPAMHAUS-ZEN:ip:zen.spamhaus.org.', 'SPAMHAUS-DBL:dom:dbl.spamhaus.org.', 'CYMRU-BOGON4:ip4:v4.bogons.cymru.com', 'CYMRU-BOGON6:ip6:v6.bogons.cymru.com']
    #config['dnswl'] = ['DNSWL:ip:list.dnswl.org.', 'SPAMHAUS-SWL:ip:swl.spamhaus.org', 'SPAMHAUS-DWL:dom:dwl.spamhaus.org']
    #config['dnswl'] = ['DNSWL:ip:list.dnswl.org.']
    config['dnswl'] = []
    config['dnsl_ttl'] = 259200 # 3 Days

    # Check if TLD exists
    config['check_tld'] = True
    config['tld_url'] = 'https://data.iana.org/TLD/tlds-alpha-by-domain.txt'

    # Check names against ratio/approx !!! SLOW, NEEDS WORK !!!
    config['check_ratio'] = False

    # Wait time between tries
    config['retry_count'] = 5
    config['retry_wait'] = 0.5

    # Unfilter
    config['unfilter'] = False
    config['unfilter_ttl'] = 5
    config['unfilter_whitelist'] = False

    # Filtering
    config['filtering'] = True
    config['filter_request'] = True
    config['filter_response'] = True
    config['use_regex'] = True
    config['use_quick_regex'] = True

    # RRTypes allowed
    config['rrtype_allow'] = False
    #config['rrtype_allow'] = ['A', 'AAAA', 'MX']

    # Smart domains (walk domains to see if blacklisted domains are prepended)
    config['smartdoms'] = False

    # Fix NOERROR and zero answer answers to NXDOMAIN
    config['fix_noerror'] = False

    # Fix NXDOMAIN to empty NOERROR
    config['fix_nxdomain'] = False

    # Fix CNAME with no address-records
    config['fix_cname'] = True
    config['fix_cname_redirect'] = False

    # Useragent
    config['useragent'] = 'DEUGNIETS/2.x'

    # Use NEXTDNS
    config['nextdns'] = False
    config['nextdns_hpm'] = True # Hardenend Privacy Mode
    config['nextdns_config'] = ''
    config['nextdns_id'] = 'DEUGNIETS'

    # GEO-Steer
    config['geo_steer'] = False

    # Get config
    if len(sys.argv) < 2:
        config = get_config(config, 'deugniets.conf')
    else:
        config = get_config(config, sys.argv[1])

    if isinstance(config['blacklist_rcode'], str):
        config['blacklist_rcode'] = dns.rcode.from_text(config['blacklist_rcode'])

    if isinstance(config['tld_rcode'], str):
        config['tld_rcode'] = dns.rcode.from_text(config['tld_rcode'])

    if config['rrtype_allow']:
        config['rrtype_allow'] = list(map(str.upper, config['rrtype_allow']))

    if config['geo_steer']:
        config['roundrobin'] = False
        config['randomroundrobin'] = False

    # Create combined regex for speed
    wl_big_rx = regex.compile(dummy)
    bl_big_rx = regex.compile(dummy)
    tld_rx = regex.compile('^.*[\.]*$', regex.I)

    # Read lists
    if not config['filtering']:
        config['use_dnsl'] = False
        config['use_regex'] = False
        config['unfilter'] = False
        config['check_tld'] = False
        config['filter_request'] = False
        config['filter_response'] = False
        config['rrtype_allow'] = False
    else:
        # Get TLDS
        if config['check_tld']:
            tlds = make_doms(get_lines(config['tld_url'], 'TLDS'))
            if tlds:
                tlds.add('command.')
                #for dom in alias:
                #    tlds.add(dom)
                #for dom in forwarder:
                #    tlds.add(dom)
                tld_rx = regex.compile('^(.*\.)*(\.|' + '|'.join('{0}'.format(x.lower()) for x in tlds if not x.startswith('#')) + ')[\.]*$', regex.I)
            else:
                logging.warning('TLDS: NO TLDs from \"{0}\"'.format(config['tld_url']))
                config['check_tld'] = False

        wl_dom, wl_ip4, wl_ip6, wl_rx, ul_dom, ul_ip4, ul_ip6, wl_geo, alias, forwarder, = read_list(config['whitelist'], 'WhiteList', wl_dom, wl_ip4, wl_ip6, wl_rx, ul_dom, ul_ip4, ul_ip6, wl_geo, alias, forwarder )
        bl_dom, bl_ip4, bl_ip6, bl_rx, _, _, _, bl_geo, _, _ = read_list(config['blacklist'], 'BlackList', bl_dom, bl_ip4, bl_ip6, bl_rx, {}, {}, {}, bl_geo, {}, {})

        if config['unfilter_whitelist']:
            ul_dom = add_list(ul_dom, wl_dom.keys(), 'UNFILTER-WHITELIST')

        wl_dom = add_list(wl_dom, alias.keys(), 'ALIAS-SOURCE')
        wl_dom = add_list(wl_dom, alias.values(), 'ALIAS-TARGET')
        wl_dom = add_list(wl_dom, forwarder.keys(), 'FORWARD-DOMAIN')

        try:
            if wl_rx:
                wl_big_rx = regex.compile('|'.join('(?:{0})'.format(x) for x in wl_rx), regex.I)

            if bl_rx:
                bl_big_rx = regex.compile('|'.join('(?:{0})'.format(x) for x in bl_rx), regex.I)

        except BaseException as err:
            logging.error('BIG-REGEX-COMPILE-ERROR: {0}'.format(err))
            sys.exit(1)

        # Whitelist Local/Private IPv4's
        private4['127.0.0.0/8'] = 'Private'
        private4['127.0.0.1/32'] = 'Private'
        private4['10.0.0.0/8'] = 'Private'
        private4['172.16.0.0/12'] = 'Private'
        private4['192.168.0.0/16'] = 'Private'

        # Whitelist Local/Private IPv6's
        private6['0::1/128'] = 'Private'
        private6['fc00::/7'] = 'Private'
        private6['fe80::/10'] = 'Private'

        for addr in config['private_addrs']:
            if addr.find(':') > -1:
                if addr not in private6:
                    private6[addzero(addr)] = 'Private'
            else:
                if addr not in private4:
                    private4[addr] = 'Private'

        for ip in private4:
            logging.info('PRIVATE-IPV4: {0}'.format(ip)) # Debug
            wl_ip4[ip] = private4[ip]

        for ip in private6:
            logging.info('PRIVATE-IPV6: {0}'.format(ip)) # Debug
            wl_ip6[ip] = private6[ip]

        if config['optimize']:
            if config['optimize_mode'] > 0: wl_dom = undom(wl_dom, wl_dom, 'WHITELIST-WHITELIST', True)
            if config['optimize_mode'] > 0: bl_dom = undom(bl_dom, bl_dom, 'BLACKLIST-BLACKLIST', True)
            if config['optimize_mode'] > 1: bl_dom = undom(bl_dom, wl_dom, 'BLACKLIST-WHITELIST', False)

            if config['optimize_mode'] > 0: l_dom = undom(ul_dom, ul_dom, 'UNFILTER-UNFILTER', True)
            if config['optimize_mode'] > 0: ul_ip4 = unip(ul_ip4, ul_ip4, False, 'UNFILTER-UNFILTER', True)
            if config['optimize_mode'] > 0: ul_ip6 = unip(ul_ip6, ul_ip6, True, 'UNFILTER-UNFILTER', True)

            if config['optimize_mode'] > 1: wl_dom = undom(wl_dom, ul_dom, 'WHITELIST-UNFILTER', True)
            if config['optimize_mode'] > 1: bl_dom = undom(bl_dom, ul_dom, 'BLACKLIST-UNFILTER', True)

            if config['optimize_mode'] > 1: wl_dom = unreg(wl_dom, wl_big_rx, 'WHITELIST-WHITELIST')
            if config['optimize_mode'] > 1: bl_dom = unreg(bl_dom, bl_big_rx, 'BLACKLIST-BLACKLIST')
            if config['optimize_mode'] > 1: bl_dom = unreg(bl_dom, wl_big_rx, 'BLACKLIST-WHITELIST')

            if config['optimize_mode'] > 0: wl_ip4 = unip(wl_ip4, wl_ip4, False, 'WHITELIST-WHITELIST', True)
            if config['optimize_mode'] > 0: bl_ip4 = unip(bl_ip4, bl_ip4, False, 'BLACKLIST-BLACKLIST', True)
            if config['optimize_mode'] > 1: bl_ip4 = unip(bl_ip4, wl_ip4, False, 'BLACKLIST-WHITELIST', False)

            if config['optimize_mode'] > 0: wl_ip6 = unip(wl_ip6, wl_ip6, True, 'WHITELIST-WHITELIST', True)
            if config['optimize_mode'] > 0: bl_ip6 = unip(bl_ip6, bl_ip6, True, 'BLACKLIST-BLACKLIST', True)
            if config['optimize_mode'] > 1: bl_ip6 = unip(bl_ip6, wl_ip6, True, 'BLACKLIST-WHITELIST', False)


        if len(wl_rx) + len(bl_rx) == 0:
            logging.info('FILTERING: REGEX filtering DISABLED due to empty lists')
            config['use_regex'] = False

        if config['use_regex'] is False and (len(wl_dom) + len(bl_dom) == 0):
            logging.info('FILTERING: REQUEST filtering DISABLED due to empty lists')
            config['filter_request'] = False

            if len(wl_ip4) + len(bl_ip4) + len(wl_ip6) + len(bl_ip6) == 0:
                logging.info('FILTERING: REQUEST filtering DISABLED due to empty lists')
                config['filter_response'] = False

        logging.info('LIST-TOTALS [WHITELIST]: {0} Domains, {1} IPv4-Addresses, {2} IPv6-Addresses and {3} Regexes'.format(len(wl_dom), len(wl_ip4), len(wl_ip6), len(wl_rx)))
        logging.info('LIST-TOTALS [BLACKLIST]: {0} Domains, {1} IPv4-Addresses, {2} IPv6-Addresses and {3} Regexes'.format(len(bl_dom), len(bl_ip4), len(bl_ip6), len(bl_rx)))
        logging.info('LIST-TOTALS [GENERIC]: {0} Aliases, {1} Selective-Forwarders, {2} UnlistDoms, {3} UnlistIP4s and {4} UnlistIP6s'.format(len(alias), len(forwarder), len(ul_dom), len(ul_ip4), len(ul_ip6)))


    wl_dom_trie = make_trie(wl_dom, 'Whitelist', False)
    del wl_dom

    bl_dom_trie = make_trie(bl_dom, 'Blacklist', False)
    del bl_dom

    alias_trie = make_trie(alias, 'Alias', True)
    del alias

    forwarder_trie = make_trie(forwarder, 'Forwarder', True)
    del forwarder

    ul_dom_trie = make_trie(ul_dom, 'Unfilter', False)
    del ul_dom

    gc.collect() # Collect garbage

    # Setup nameservers
    setup_nameservers()

    # AbuseIPDB setup
    if config['abuseipdbkey']:
        logging.info('ABUSEIPDB: API-Key = {0}'.format(config['abuseipdbkey']))

    # Setup requests sessions
    requests_session = requests.Session()
    #requests_session.mount('https://', HTTP20Adapter())
    #abuseipdb_session = requests.Session()

    # Geo-IP
    if config['geodb']:
        logging.info('GEO-DB: Loading database from {0} ...'.format(config['geodb']))
        geoip = geoip2.database.Reader(config['geodb'])
        logging.info('GEO-DB: Loading database finished')

    # Run
    run_server()

    # Terminate
    requests_session.close()
    #abuseipdb_session.close()
 
    logging.info('SERVER: DeugNietS Stopped')

    sys.exit(0)

# EOF
