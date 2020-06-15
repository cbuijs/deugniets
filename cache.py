# cache.py - v2.30-20200615 - cbuijs@chrisbuijs.com
# Based upon: https://github.com/dnaeon/py-vconnector/blob/master/src/vconnector/cache.py

import logging
import threading

import time
from collections import OrderedDict, namedtuple

__all__ = ['CachedObject', 'CacheInventory']

_CachedObjectInfo = namedtuple('CachedObjectInfo', ['name', 'hits', 'ttl', 'timestamp', 'expires'])


class CachedObject(object):
    def __init__(self, name, obj, ttl):
        """
        Initializes a new cached object

        Args:
            name               (str): Human readable name for the cached entry
            obj               (type): Object to be cached
            ttl                (int): The TTL in seconds for the cached object
        """
        self.obj = obj
        self.name = name
        self.hits = 0
        self.ttl = ttl
        self.timestamp = int(time.time())
        self.expires = self.timestamp + self.ttl

class CacheInventory(object):
    """
    Inventory for cached objects

    """
    def __init__(self, maxsize=512, housekeeping=30, name='CACHE', minttl=0, maxttl=0, cachelog=False):
        """
        Initializes a new cache inventory

        Args:
            maxsize      (int) : Upperbound limit on the number of items that will be stored in the cache inventory
            housekeeping (int) : Time in seconds to perform periodic cache housekeeping
            name         (str) : Name of cache
            minttl       (int) : Minimum TTL
            maxttl       (int) : Maximum TTL
            cachelog     (bool): Logging
        """

        if maxsize < 0:
            logging.error('CACHE [{0}]: Cache inventory size is {1}, cannot be negative!'.format(self.name, maxsize))
            raise

        if housekeeping < 0:
            logging.error('CACHE [{0}]: Cache housekeeping period is {1}, cannot be negative!'.format(self.name, housekeeping))
            raise

        if minttl < 0:
            logging.error('CACHE [{0}]: Cache minttl is {1}, cannot be negative!'.format(self.name, minttl))
            raise

        if maxttl < 0 or (maxttl > 0 and maxttl < minttl):
            logging.error('CACHE [{0}]: Cache minttl is {1}, cannot be negative or lower then minttl ({2})!'.format(self.name, maxttl, minttl))
            raise

        self._cache = OrderedDict()
        self.maxsize = maxsize
        self.housekeeping = housekeeping
        self.name = name
        self.minttl = minttl
        self.maxttl = maxttl
        self.lock = threading.RLock()
        self._schedule_housekeeper()
        self.cachelog = cachelog

    def __len__(self):
        with self.lock:
            return len(self._cache)

    def __contains__(self, key):
        with self.lock:
            if key not in self._cache:
                return False

            item = self._cache[key]
            return not self._has_expired(item, 'CONTAINS')

    def _has_expired(self, item, comment):
        """
        Checks if a cached item has expired and removes it if needed

        Args:
            item (CachedObject): A cached object to lookup

        Returns:
            bool: True if the item has expired, False otherwise
        """

        with self.lock:
            if int(time.time()) > item.expires:
                if self.cachelog: logging.info('CACHE-EXPIRED-{0} [{1}]: Purged \"{2}\" (Start:{3} End:{4} TTL:{5})'.format(comment, self.name, self.info(item.name).name, time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(item.timestamp)), time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(item.expires)), item.ttl))
                self._cache.pop(item.name)
                return True
            return False

    def _schedule_housekeeper(self):
        """
        Schedules the next run of the housekeeper
        """

        if self.housekeeping > 0:
            t = threading.Timer(
                interval=self.housekeeping,
                function=self._housekeeper
            )
            t.setDaemon(True)
            t.start()

    def _housekeeper(self):
        """
        HouseKeeper
        """

        with self.lock:
            self._purge('SCHEDULER')
            self._schedule_housekeeper()

    def _purge(self, comment):
        """
        Remove expired entries from the cache on regular basis
        """

        with self.lock:
            expired = 0
            items = list(self._cache.values())
            for item in items:
                if self._has_expired(item, comment):
                    expired += 1

            if expired > 0:
                if self.cachelog: logging.info('CACHE-STATS [{0}]: Purged {1} item(s), {2} left'.format(self.name, expired, len(self._cache)))

    def add(self, obj):
        """
        Add an item to the cache inventory

        If the upperbound limit has been reached then the last item is being removed from the inventory.

        Args:
            obj (CachedObject): A CachedObject instance to be added
        """

        if not isinstance(obj, CachedObject):
            logging.error('CACHE [{0}]: No CachedObject!'.format(self.name))
            raise

        with self.lock:
            if 0 < self.maxsize == len(self._cache):
                self._purge('CACHE-FULL') # Clear all expired

            while 0 < self.maxsize == len(self._cache):
                first = list(self._cache.keys())[0] # Get oldest added entry !!! Maybe change to get earliest to expire ones
                popped = self._cache.pop(first)
                left = int(popped.expires - time.time())
                if self.cachelog: logging.warning('CACHE-FULL [{0}]: Purged \"{1}\" (TTL-Left: {2})'.format(self.name, popped.name, left))

            if self.minttl > 0 and obj.ttl < self.minttl:
                if self.cachelog: logging.info('CACHE-MIN-TTL [{0}]: Increased TTL for \"{1}\" from {2} to {3}'.format(self.name, obj.name, obj.ttl, self.minttl))
                obj.ttl = self.minttl

            if self.maxttl > 0 and obj.ttl > self.maxttl:
                if self.cachelog: logging.info('CACHE-MAX-TTL [{0}]: Decreased TTL for \"{1}\" from {2} to {3}'.format(self.name, obj.name, obj.ttl, self.maxttl))
                obj.ttl = self.maxttl

            obj.expires = obj.timestamp + obj.ttl

            self._cache[obj.name] = obj
            obj = self.info(name=obj.name)

            if self.cachelog: logging.info('CACHED [{0} #{4}]: \"{1}\" (TTL:{2} Start:{3})'.format(self.name, obj.name, obj.ttl, time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(obj.timestamp)), len(self._cache)))

    def get(self, name, default=None):
        """
        Retrieve an object from the cache inventory

        Args:
            name (str): Name of the cache item to retrieve

        Returns:
            The cached object if found, None otherwise
        """

        with self.lock:
            if name not in self._cache:
                return default

            item = self._cache[name]
            if self._has_expired(item, 'GET'):
                return default

            item.hits += 1
            obj = self.info(name=item.name)
            left = int(obj.expires - int(time.time()))
            if self.cachelog: logging.info('CACHE-HIT [{0}]: \"{1}\" (TTL:{2}) - {3} Hits'.format(self.name, obj.name, left, obj.hits))

            return item.obj

    def entries(self):
        with self.lock:
            return self._cache.values()

    def clear(self):
        """
        Remove all items from the cache
        """

        with self.lock:
            while self._cache:
                popped = self._cache.popitem()
                if self.cachelog: logging.info('CACHE-CLEAR [{0}]: Purged \"{1}\"'.format(self.name, popped[0]))
            self._cache.clear()
        if self.cachelog: logging.debug('CACHE-CLEAR [{0}]: Cache Cleared'.format(self.name))

    def info(self, name):
        """
        Get statistics about a cached object

        Args:
            name (str): Name of the cached object
        """

        with self.lock:
            if name not in self._cache:
                return None

            item = self._cache[name]
            return _CachedObjectInfo(item.name, item.hits, item.ttl, item.timestamp, item.expires)

# <EOF>
