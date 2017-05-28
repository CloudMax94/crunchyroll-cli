#!/usr/bin/python3
import base64
import concurrent.futures
import copy
import datetime
import getpass
import hashlib
import json
import math
import os
import random
import re
import signal
import string
import subprocess
import time
import zlib
from shlex import quote
from sys import argv, exit
from binascii import unhexlify, hexlify
from tqdm import tqdm

import requests
from Crypto.Cipher import AES
from bs4 import BeautifulSoup
from dateutil import tz

# Where should the cache file be stored?
# This file is used to store generated device id, session id, username and password
CACHE_PATH = os.path.dirname(os.path.realpath(__file__)) + '/.crcache'
# Where should the subtitle file be stored?
SUBTITLE_TEMP_PATH = os.path.dirname(os.path.realpath(__file__)) + '/.ass'
# Where should the temporary RTMP info file be stored? (used to extract info from stderr)
RTMP_INFO_TEMP_PATH = os.path.dirname(os.path.realpath(__file__)) + '/.rtmpinfo'
# Where downloads are saved. Available variables: collection, media_name, episode
DOWNLOAD_PATH = os.path.dirname(os.path.realpath(__file__)) + '/downloads/{collection}/{collection} - e{episode:02d}'

# How many days must pass before the show isn't considered followed
QUEUE_FOLLOWING_THRESHOLD = 14
# How many percentage of the video you must've seen for it to count as seen
QUEUE_WATCHED_THRESHOLD = 0.8
# Should it authenticate automatically on startup?
AUTHENTICATE = True
# Should notifications be sent when a new episode of a series you're following becomes available?
NOTIFICATIONS = True
# Update playhead automatically every n seconds while watching media (0 = never)
AUTO_PLAYHEAD = 0
# Should playhead be updated without asking after watching media?
AUTO_PLAYHEAD_END = False
# How many seconds should the queue be cached before expiring
QUEUE_CACHE_EXPIRES = 60 * 60

# END OF CONFIGURATION

API_HOST = 'api.crunchyroll.com'
RPC_API_HOST = 'www.crunchyroll.com'
USER_AGENT = 'Mozilla/5.0 (X11; Linux x86_64; rv:51.0) Gecko/20100101 Firefox/51.0'

queue = []
ram_cache = None
last_watched_timestamp = None  # Only used to transfer timestamp from authenticate to load_queue...


class Color:
    PURPLE = '\033[95m'
    CYAN = '\033[96m'
    DARKCYAN = '\033[36m'
    BLUE = '\033[94m'
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    RED = '\033[91m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'
    END = '\033[0m'


colors = {}
for i in dir(Color):
    if not i.startswith("__"):
        colors[i] = getattr(Color, i)

print_overridable_len = 0


# If string is empty, it ends override by cleaning up the current line
def print_overridable(pstring='', end=False):
    global print_overridable_len
    old_len = print_overridable_len
    cleanstr = pstring
    for e, v in colors.items():
        cleanstr = cleanstr.replace(v, '')
    print_overridable_len = len(cleanstr)
    if old_len > print_overridable_len:
        pstring += ' ' * (old_len - print_overridable_len)
    if end:
        print_overridable_len = 0
        print(pstring)
    else:
        print(pstring, end="\r", flush=True)


# End override by placing text on a new line
def print_under(pstring=''):
    global print_overridable_len
    if len(pstring):
        print('\n' + pstring)
    else:
        print('')
    print_overridable_len = 0


def input_yes(question):
    answer = input(question + ' (Y/N)? ')
    return answer.lower() == 'y'


def mmss(seconds):
    stamp = str(datetime.timedelta(seconds=int(float(seconds))))
    if stamp.startswith("0:"):
        stamp = stamp[2:]
    return stamp


def timestamp_to_datetime(ts):
    part1 = datetime.datetime.strptime(ts[:-6], '%Y-%m-%dT%H:%M:%S')
    part2 = datetime.timedelta(hours=int(ts[-5:-3]), minutes=int(ts[-2:])) * -int(ts[-6:-5] + '1')
    return (part1 + part2).replace(tzinfo=tz.tzutc()).astimezone(tz.tzlocal())


# TODO: Handle re-authentication when session has expired directly in the API calls
def call_api(name, params, secure=False):
    protocol = "http"
    if secure:
        protocol += "s"
    headers = {
        'Host': API_HOST,
        'User-Agent': USER_AGENT
    }
    sess_id = get_cache("session_id")
    if sess_id:
        params['session_id'] = sess_id
    resp = requests.post('{}://{}/{}.0.json'.format(protocol, API_HOST, name), headers=headers, params=params)
    resp.encoding = 'utf-8'
    return resp.json()


def call_rpc(name, params):
    headers = {
        'Host': RPC_API_HOST,
        'User-Agent': USER_AGENT
    }
    params['req'] = name
    resp = requests.get('http://{}/xml/'.format(RPC_API_HOST), headers=headers, params=params,
                        cookies={'sess_id': get_cache("session_id")})
    resp.encoding = 'utf-8'
    return resp


def generate_key(mediaid):
    # Below: Do some black magic
    eq1 = int(int(math.floor(math.sqrt(6.9) * math.pow(2, 25))) ^ mediaid)
    eq2 = int(math.floor(math.sqrt(6.9) * math.pow(2, 25)))
    eq3 = str((mediaid ^ eq2) ^ (mediaid ^ eq2) >> 3 ^ eq1 * 32).encode('utf-8')
    # Below: Creates a 160-bit SHA1 hash padded to 256-bit using zeroes
    sha_hash = hashlib.sha1(create_string() + eq3).digest() + b'\x00' * 12
    return sha_hash


def create_string():
    arg_array = [1, 2]
    for fib in range(20):
        arg_array.append(arg_array[-1] + arg_array[-2])
    final_string = ''
    for arg in arg_array[2:]:
        final_string += chr(arg % 97 + 33)
    return final_string.encode('utf-8')


def decode_subtitles(subid, iv, data):
    key = generate_key(subid)
    iv = base64.b64decode(iv)
    data = base64.b64decode(data)
    cipher = AES.new(key, AES.MODE_CBC, iv)
    decrypteddata = cipher.decrypt(data)
    return zlib.decompress(decrypteddata)


def convert(script):
    soup = BeautifulSoup(script, 'xml')
    header = soup.find('subtitle_script')
    header = "[Script Info]\nTitle: " + header['title'] + "\nScriptType: v4.00+\nWrapStyle: " + header['wrap_style'] \
             + "\nPlayResX: " + header['play_res_x'] + "\nPlayResY: " + header['play_res_y'] + "\n\n"
    styles = "[V4+ Styles]\nFormat: Name, Fontname, Fontsize, PrimaryColour, SecondaryColour, OutlineColour, " \
             "BackColour, Bold, Italic, Underline, StrikeOut, ScaleX, ScaleY, Spacing, Angle, BorderStyle, " \
             "Outline, Shadow, Alignment, MarginL, MarginR, MarginV, Encoding\n"
    events = "\n[Events]\nFormat: Layer, Start, End, Style, Name, MarginL, MarginR, MarginV, Effect, Text\n"
    stylelist = soup.findAll('style')
    eventlist = soup.findAll('event')

    for style in stylelist:
        if style['scale_x'] or style['scale_y'] == '0':
            style['scale_x'], style['scale_y'] = '100', '100'  # Fix for Naruto 1-8 where it's set to 0 but ignored
        styles += "Style: " + style['name'] + "," + style['font_name'] + "," + style['font_size'] + "," \
                  + style['primary_colour'] + "," + style['secondary_colour'] + "," + style['outline_colour'] + "," \
                  + style['back_colour'] + "," + style['bold'] + "," + style['italic'] + "," \
                  + style['underline'] + "," + style['strikeout'] + "," + style['scale_x'] + "," \
                  + style['scale_y'] + "," + style['spacing'] + "," + style['angle'] + "," \
                  + style['border_style'] + "," + style['outline'] + "," + style['shadow'] + "," \
                  + style['alignment'] + "," + style['margin_l'] + "," + style['margin_r'] + "," \
                  + style['margin_v'] + "," + style['encoding'] + "\n"

    for event in eventlist:
        events += "Dialogue: 0," + event['start'] + "," + event['end'] + "," + event['style'] + "," \
                  + event['name'] + "," + event['margin_l'] + "," + event['margin_r'] + "," + event['margin_v'] \
                  + "," + event['effect'] + "," + event['text'] + "\n"

    formattedsubs = header + styles + events
    return formattedsubs


def get_cache(key=None):
    def _get_cache():
        global ram_cache
        if ram_cache:
            return ram_cache
        if os.path.isfile(CACHE_PATH):
            with open(CACHE_PATH, 'r') as file:
                fcache = file.read()
                if fcache != "":
                    fcache = json.loads(fcache)
                    return fcache
        return {}

    cache = _get_cache()
    if key is not None:
        if key in cache:
            return cache[key]
        return None
    return cache


def set_cache(arg1, value=None):
    global ram_cache
    if value is not None:
        cache = get_cache()
        cache[arg1] = value
    else:
        cache = arg1
    # We use atomic saving in case of a screw up that would remove all user data
    tmp = os.path.dirname(CACHE_PATH) + '/~' + os.path.basename(CACHE_PATH)
    with open(tmp, 'w') as f:
        try:
            json.dump(cache, f)
            f.flush()
            os.fsync(f.fileno())
            f.close()
            os.rename(tmp, CACHE_PATH)
        except TypeError:  # includes simplejson.decoder.JSONDecodeError
            print(Color.RED + 'Could not save cache, error encoding JSON' + Color.END)
            f.close()
            os.remove(tmp)


def unset_cache(*keys):
    cache = get_cache()
    for key in set(keys):
        if key in cache:
            del cache[key]
    set_cache(cache)


def get_device_id():
    device_id = get_cache("device_id")
    if device_id is not None:
        return device_id
    # Create a random device id and cache it
    char_set = string.ascii_letters + string.digits
    device_id = "".join(random.sample(char_set, 32))
    set_cache("device_id", device_id)
    return device_id


def create_session():
    data = {
        "device_id": get_device_id(),
        "device_type": "com.crunchyroll.iphone",
        "access_token": "QWjz212GspMHH9h"
    }
    expires = get_cache("expires")
    auth = get_cache("auth")
    if expires and expires < time.time():
        unset_cache("expires", "auth")
        print_overridable(Color.RED + 'Authentication has expired, must reauthenticate' + Color.END, True)
    elif auth:
        data["auth"] = auth

    print_overridable('Creating session...')
    unset_cache('session_id')  # The call will fail if you have an expired session set
    resp = call_api('start_session', data)

    if resp['error']:
        print_overridable(Color.RED + 'Error: ' + resp['message'] + Color.END, True)
        return None
    else:
        print_overridable(Color.GREEN + 'Session created' + Color.END, True)
        sess_id = resp['data']['session_id']
        if resp['data']['auth']:
            finish_auth(sess_id, resp['data']['auth'], resp['data']['expires'])
            return None  # We return None to short-circuit the caller since the session is already authenticated
        return sess_id


def authenticate_session(user, password, sess_id):
    data = {
        "account": user,
        "password": password,
        "session_id": sess_id
    }
    print_overridable('Authenticating...')
    resp = call_api('login', data, True)
    if resp['error']:
        print_overridable(Color.RED + 'Error: ' + resp['message'] + Color.END, True)
    else:
        finish_auth(sess_id, resp['data']['auth'], resp['data']['expires'])


def finish_auth(sess_id, auth, expires):
    set_cache("auth", auth)
    set_cache("expires", timestamp_to_datetime(expires).timestamp())
    set_cache("session_id", sess_id)
    print_overridable(Color.GREEN + 'You are now authenticated' + Color.END, True)


# TODO: Currently the session is dropped entirely if the authentication fails. We want to cache and re-use it on the next attempt!
def authenticate(args):
    global last_watched_timestamp
    sess_id = get_cache("session_id")
    if sess_id and "new" not in args:
        # This call is used to determine if session is valid, as well as obtaining timestamp to determine if queue is
        # outdated!
        resp = call_api('recently_watched', {
            'media_types': 'anime|drama',
            'offset': 0,
            'limit': 1,
            'fields': 'timestamp'
        })
        if not resp['error']:
            last_watched_timestamp = resp['data'][0]['timestamp']
            print(Color.GREEN + 'You are still authenticated' + Color.END)
            return
        print(Color.RED + 'Session has expired' + Color.END)
        unset_cache('session_id')

    sess_id = create_session()
    if sess_id:
        user = get_cache("user")
        if not user:
            user = input('Username: ')
            if input_yes("Remember username"):
                set_cache("user", user)
                print(Color.GREEN + 'Username saved' + Color.END)
        password = get_cache("password")
        if not password:
            password = getpass.getpass()
            if input_yes("Remember password"):
                set_cache("password", password)
                print(Color.GREEN + 'Password saved' + Color.END)
        authenticate_session(user, password, sess_id)


def update_notifications():
    notifications = get_cache('notifications')
    if not notifications:
        notifications = {}
    now = datetime.datetime.utcnow().replace(tzinfo=tz.tzutc())
    for item in queue:
        media = item['most_likely_media']
        if item['last_watched_media_playhead'] > 0:
            air = media['available_time']
            series_id = item['series']['series_id']
            if air > now:
                air_seconds = int(time.mktime(air.timetuple()))
                if series_id not in notifications or air_seconds != notifications[series_id][1]:
                    if series_id in notifications:  # An outdated notification is set, remove it!
                        subprocess.Popen(["atrm", notifications[series_id][0]])
                    proc = subprocess.Popen(
                        ['at', air.strftime("%H%M %d.%m.%y")],
                        stdin=subprocess.PIPE,
                        stdout=subprocess.DEVNULL,
                        stderr=subprocess.PIPE
                    )
                    if media['episode_number']:
                        episode = ' episode ' + media['episode_number']
                    else:
                        episode = ''
                    cmd = "notify-send 'Crunchyroll CLI' '{}{} is now available.'".format(
                        media['collection_name'].replace("'", "'\\''"),
                        episode
                    )
                    output = proc.communicate(input=cmd.encode())[1]
                    result = re.search(b'job (\d+)', output)
                    if result:
                        notifications[item['series']['series_id']] = [result.group(1).decode("utf-8"), air_seconds]
            elif series_id in notifications:
                del notifications[series_id]
    set_cache('notifications', notifications)


def save_queue():
    global queue
    savequeue = copy.deepcopy(queue)
    for index, item in enumerate(savequeue):
        for media in ['most_likely_media']:  # , 'last_watched_media'
            savequeue[index][media]['available_time'] = savequeue[index][media]['available_time'].replace(
                tzinfo=tz.tzutc()).timestamp()  # We save the queue as an UTC integer
    set_cache('queue', savequeue)
    set_cache('queue_timestamp', int(time.time()))


# TODO: Force expire the cache when you're past the air time of a show you're following (Maybe this should apply whenever queue is retrieved?)
def load_queue():
    global queue
    if not get_cache("session_id"):
        return
    print_overridable('Checking cache for queue...')
    queue_timestamp = get_cache('queue_timestamp')
    cached_queue = get_cache('queue')
    if not cached_queue or not queue_timestamp:
        print_overridable('No queue cached', True)
        return False
    if time.time() > queue_timestamp + QUEUE_CACHE_EXPIRES:  # Queue automatically expires after a set amount of time
        seconds = int(time.time() - queue_timestamp)
        if seconds >= 60 * 2:  # >= Two minutes
            if seconds >= 60 * 60 * 2:  # >= Two hours
                if seconds >= 60 * 60 * 24 * 2:  # >= Two days
                    text = str(int(seconds / 60 / 60 / 24)) + " days"
                else:
                    text = str(int(seconds / 60 / 60)) + " hours"
            else:
                text = str(int(seconds / 60)) + " minutes"
        else:
            text = str(seconds) + " seconds"
        queue = []
        unset_cache('queue')
        unset_cache('queue_timestamp')
        print_overridable('Cached queue is {} old and has expired'.format(text), True)
        return False
    else:  # If queue hasn't expired, we compare the latest recently_watched entry to see if the queue is outdated
        print_overridable('Checking if cache is outdated...')
        if last_watched_timestamp:  # The recently_watched call used for authentication succeeded, use the response from that
            timestamp = last_watched_timestamp
        else:  # otherwise we'll just make another call to it now that we're authenticated
            resp = call_api('recently_watched', {
                'media_types': 'anime|drama',
                'offset': 0,
                'limit': 1,
                'fields': 'timestamp'
            })
            if resp['error']:
                if resp['code'] == "bad_session":
                    msg = "You do not have a valid session"
                    unset_cache("session_id")
                else:
                    msg = "{} ({})".format(resp['message'], resp['code'])
                print_overridable(Color.RED + 'Error: Could not determine if queue is outdated. ' + msg + Color.END,
                                  True)
                return False
            else:
                timestamp = resp['data'][0]['timestamp']
        # NOTE: Crunchyroll returns a UTC timestamp even though it says -07:00 on it, so we ignore the timezone part
        timestamp = (datetime.datetime.strptime(timestamp[:-6], '%Y-%m-%dT%H:%M:%S')).replace(
            tzinfo=tz.tzutc()).astimezone(tz.tzlocal())
        timestamp = int(time.mktime(timestamp.timetuple()))
        print_overridable('', True)
        if timestamp > queue_timestamp:
            unset_cache('queue')
            unset_cache('queue_timestamp')
            print_overridable('Cached queue was outdated and has been purged', True)
            return False
    print_overridable(Color.GREEN + 'Queue loaded' + Color.END, True)
    for index, item in enumerate(cached_queue):
        for media in ['most_likely_media']:  # , 'last_watched_media'
            cached_queue[index][media]['available_time'] = datetime.datetime.fromtimestamp(
                cached_queue[index][media]['available_time']).replace(tzinfo=tz.tzlocal())
    queue = cached_queue
    return True


def update_queue():
    global queue
    if not get_cache("session_id"):
        if queue:
            print(Color.YELLOW + 'Error: Could not update queue. You are not authenticated' + Color.END)
        else:
            print(Color.RED + 'Warning: Could not load queue. You are not authenticated' + Color.END)
        return

    if queue:
        print_overridable('Updating queue...')
        result_str = 'Queue updated'
    else:
        print_overridable('Loading queue...')
        result_str = 'Queue loaded'
    data = {
        'fields': 'last_watched_media_playhead,most_likely_media,media.name,media.episode_number,'
                  'media.available_time,media.duration,media.collection_name,media.url,series,series.name,'
                  'series.series_id,media.playhead '
    }

    resp = call_api('queue', data)
    if resp['error']:
        if resp['code'] == "bad_session":
            msg = "Your session has expired. You are no longer authenticated"
            unset_cache("session_id")
        else:
            msg = "{} ({})".format(resp['message'], resp['code'])
        print_overridable(Color.RED + 'Error: Could not fetch queue. ' + msg + Color.END, True)
    else:
        queue = resp['data']
        for index, item in enumerate(queue):
            # Add missing integer values, and convert them from string to int
            for key in ['last_watched_media_playhead']:
                val = item[key]
                if not val:
                    val = 0
                else:
                    val = int(val)
                queue[index][key] = val
            for media in ['most_likely_media']:  # , 'last_watched_media'
                if not item[media]:
                    continue
                for key in ['duration', 'playhead']:
                    val = item[media][key]
                    if not val:
                        val = 0
                    else:
                        val = int(val)
                    queue[index][media][key] = val
                queue[index][media]['available_time'] = timestamp_to_datetime(queue[index][media]['available_time'])
        print_overridable(Color.GREEN + result_str + Color.END, True)
        save_queue()
        if NOTIFICATIONS:
            update_notifications()


def run_media(pageurl, playhead=0):
    while True:
        mediaid = re.search(r'[^\d](\d{6})(?:[^\d]|$)', pageurl).group(1)

        data = {
            'media_id': mediaid,
            'video_format': '108',
            'video_quality': '80',
            'current_page': pageurl
        }

        print_overridable('Fetching media information...')
        config = call_rpc('RpcApiVideoPlayer_GetStandardConfig', data)
        print_overridable()
        if config.status_code != 200:
            print(Color.RED + 'Error: ' + config.text + Color.END)
            return

        # What is this even? Does it catch some specific media or 404 pages?
        if len(config.text) < 100:
            print(config.url)
            print(config.text)
            return

        config = BeautifulSoup(config.text, 'lxml-xml')

        # Check for errors
        error = config.find('error')
        if error:
            print(Color.RED + 'Error: ' + error.msg.text + Color.END)
            return

        # Check if media is unavailable
        error = config.find('upsell')
        if error:
            print(Color.RED + 'Error: Media is only available for premium members' + Color.END)
            return

        collection_name = config.series_title.text
        print(Color.BOLD + collection_name + Color.END)
        media_name = config.episode_title.text
        episode = config.episode_number.text
        if episode:
            print(Color.BOLD + 'Episode:    ' + Color.END + episode)
        if media_name:
            print(Color.BOLD + 'Title:      ' + Color.END + media_name)
        duration = config.duration.text
        print(Color.BOLD + 'Duration:   ' + Color.END + '{}'.format(mmss(duration)))

        sub = config.find('subtitle', attrs={'link': None})
        if sub:
            print_overridable('Preparing subtitles...')
            _id = int(sub['id'])
            _iv = sub.iv.text
            _subdata = sub.data.text
            open(SUBTITLE_TEMP_PATH, 'w').write(convert(decode_subtitles(_id, _iv, _subdata).decode('utf-8')))

        print_overridable('Fetching stream information...')

        streamconfig = BeautifulSoup(call_rpc('RpcApiVideoEncode_GetStreamInfo', data).text, 'lxml-xml')
        streamconfig.encoding = 'utf-8'

        print_overridable('Starting stream...')

        subarg = []
        if sub:
            subarg = ['--sub-file', quote(SUBTITLE_TEMP_PATH)]

        rtmpinfo = None
        if not streamconfig.host.text:
            # If by any chance that GetStreamInfo returns HLS; it should never get to this point
            url = streamconfig.file.text
            proccommand = ['mpv', url] + subarg
            proc = subprocess.Popen(
                proccommand,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.PIPE,
                bufsize=1
            )

        else:
            host = streamconfig.host.text
            file = streamconfig.file.text
            if re.search('fplive\.net', host):
                url1, = re.findall('.+/c\d+', host)
                url2, = re.findall('c\d+\?.+', host)
            else:
                url1, = re.findall('.+/ondemand/', host)
                url2, = re.findall('ondemand/.+', host)

            proccommand = ['rtmpdump',
                           '-r', url1,
                           '-a', url2,
                           '-f', 'WIN 11,8,800,50',
                           '-m', '15',
                           '-W', 'http://www.crunchyroll.com/vendor/ChromelessPlayerApp-c0d121b.swf',
                           '-p', pageurl,
                           '-y', file,
                           '--start', str(playhead)]
            rtmpinfo = open(RTMP_INFO_TEMP_PATH, 'w+')
            rtmpproc = subprocess.Popen(proccommand,
                                        stderr=rtmpinfo,
                                        # NOTE: There is probably a much better way to obtain stderr without
                                        # blocking, but I gave up and went with whatever worked
                                        stdout=subprocess.PIPE
                                        )
            proc = subprocess.Popen(['mpv', '--force-seekable=yes', '--rebase-start-time=no', '-'] + subarg,
                                    stdin=rtmpproc.stdout,
                                    stderr=subprocess.PIPE,
                                    stdout=subprocess.DEVNULL,
                                    bufsize=1
                                    )
            rtmpproc.stdout.close()  # Allow rtmpproc to receive a SIGPIPE if proc exits.

        set_cache('previous_episode', pageurl)
        set_cache('previous_playhead', playhead)
        if playhead:
            start_position = mmss(playhead) + '-'
        else:
            start_position = ''
        download_position = playhead
        last_update = time.time()
        playhead_update = last_update
        playhead_count = 0

        def update_playhead(media_id, plyhead):
            nonlocal playhead_count
            resp = call_rpc('RpcApiVideo_VideoView', {
                'media_id': media_id,
                'cbcallcount': playhead_count,
                'cbelapsed': 30,
                'playhead': plyhead
            })
            if resp.status_code != 200:
                print_overridable(Color.RED + 'Error: ' + resp.text + Color.END, True)
                return False
            else:
                playhead_count += 1
                print_overridable((Color.GREEN + 'Playhead was updated to {}' + Color.END).format(mmss(plyhead)), True)
                return True

        rtmp_metadata = None
        rtmp_info_done = False
        with concurrent.futures.ThreadPoolExecutor(max_workers=2) as executor:
            while True:
                line = proc.stderr.readline().decode("utf-8")
                if line == '' and proc.poll() is not None:
                    break

                if rtmpinfo:
                    rtmpinfo.seek(0)
                    for line2 in rtmpinfo.readlines():
                        if line2.rstrip() == '':
                            continue
                        r = re.search('([\d.]+) kB / ([\d.]+) sec', line2)
                        if r:
                            download_position = float(r.group(2))
                        elif not rtmp_info_done:
                            r = re.search('INFO: ([^ ]+):', line2)
                            if r:
                                if rtmp_metadata:
                                    print_overridable(Color.BOLD + 'Video:      ' + Color.END + '{}x{} ({})'.format(
                                        int(float(rtmp_metadata['width'])), int(float(rtmp_metadata['height'])),
                                        rtmp_metadata['videocodecid']), True)
                                    print(Color.BOLD + 'Audio:      ' + Color.END + '{}hz ({})'.format(
                                        int(float(rtmp_metadata['audiosamplerate'])), rtmp_metadata['audiocodecid']))
                                    rtmp_info_done = True
                                else:
                                    rtmp_metadata = {}
                            else:
                                r = re.search('INFO: {3}([^ ]+) +(.+)', line2)
                                if r:
                                    rtmp_metadata[r.group(1)] = r.group(2)

                    # Empty the file to prevent taking up unnecessary space
                    rtmpinfo.seek(0)
                    rtmpinfo.truncate()

                timestamp = re.search('V: (\d{2}:\d{2}:\d{2}) / (\d{2}:\d{2}:\d{2})', line)
                if timestamp:
                    current = [int(t) for t in timestamp.group(1).split(":")]
                    playhead = (current[0] * 60 + current[1]) * 60 + current[2]
                    now = time.time()
                    if get_cache("session_id") and AUTO_PLAYHEAD and now >= playhead_update + AUTO_PLAYHEAD:
                        playhead_update = now
                        executor.submit(update_playhead, mediaid, playhead)
                    if now >= last_update + 5:
                        set_cache('previous_playhead', playhead)
                        last_update = now
                    if "Paused" in line:
                        paused = ' [PAUSED]'
                    else:
                        paused = ''
                    print_overridable((
                                          Color.BOLD + 'Downloaded:' + Color.END + ' {}{} ' + Color.BOLD + 'Playhead:'
                                          + Color.END + ' {}{}').format(start_position, mmss(download_position),
                                                                        mmss(playhead), paused))
        print_under()
        set_cache('previous_playhead', playhead)
        if rtmpinfo:
            rtmpinfo.close()
            os.remove(RTMP_INFO_TEMP_PATH)
        if sub:
            os.remove(SUBTITLE_TEMP_PATH)

        if get_cache("session_id") and (AUTO_PLAYHEAD_END or input_yes(
                'Do you want to update playhead to {}/{}'.format(mmss(playhead), mmss(duration)))):
            print_overridable('Updating playhead...')
            update_playhead(mediaid, playhead)

        if playhead_count:  # if playhead was updated at least once, we need to update the queue
            update_queue()

        next_episode = config.find('nextUrl').text
        if next_episode != "":
            if input_yes('Another episode is available, do you want to watch it'):
                pageurl = next_episode
                playhead = 0
            else:
                break
        else:
            print(Color.RED + 'No more episodes available' + Color.END)
            break


def safe_filename(filename):
    keepcharacters = (' ','.','_')
    return "".join(c for c in filename if c.isalnum() or c in keepcharacters).rstrip()


def download_media(pageurl):
    mediaid = re.search(r'[^\d](\d{6})(?:[^\d]|$)', pageurl).group(1)

    data = {
        'media_id': mediaid,
        'video_format': '108',
        'video_quality': '80',
        'current_page': pageurl
    }

    print_overridable('Fetching media information...')
    config = call_rpc('RpcApiVideoPlayer_GetStandardConfig', data)
    print_overridable()
    if config.status_code != 200:
        print(Color.RED + 'Error: ' + config.text + Color.END)
        return

    # What is this even? Does it catch some specific media or 404 pages?
    if len(config.text) < 100:
        print(config.url)
        print(config.text)
        return

    config = BeautifulSoup(config.text, 'lxml-xml')

    # Check for errors
    error = config.find('error')
    if error:
        print(Color.RED + 'Error: ' + error.msg.text + Color.END)
        return

    # Check if media is unavailable
    error = config.find('upsell')
    if error:
        print(Color.RED + 'Error: Media is only available for premium members' + Color.END)
        return

    collection_name = config.series_title.text
    print(Color.BOLD + collection_name + Color.END)
    media_name = config.episode_title.text
    episode = config.episode_number.text
    if episode:
        print(Color.BOLD + 'Episode:    ' + Color.END + episode)
    if media_name:
        print(Color.BOLD + 'Title:      ' + Color.END + media_name)
    duration = config.duration.text

    basepath = DOWNLOAD_PATH.format(collection=safe_filename(collection_name),
                                    media_name=safe_filename(media_name),
                                    episode=int(episode)
                                    )
    subname = basepath + '.eng.ass'
    sub = config.find('subtitle', attrs={'link': None})
    if sub:
        print_overridable('Downloading subtitles...')
        _id = int(sub['id'])
        _iv = sub.iv.text
        _subdata = sub.data.text
        if not os.path.exists(os.path.dirname(subname)):
            try:
                os.makedirs(os.path.dirname(subname))
            except OSError as exc: # Guard against race condition
                if exc.errno != errno.EEXIST:
                    raise
        open(subname, 'w').write(convert(decode_subtitles(_id, _iv, _subdata).decode('utf-8')))

    print_overridable('Fetching stream information...')

    streamconfig = BeautifulSoup(call_rpc('RpcApiVideoEncode_GetStreamInfo', data).text, 'lxml-xml')
    streamconfig.encoding = 'utf-8'

    host = streamconfig.host.text
    file = streamconfig.file.text
    if not file and not host:
        # If stream info doesn't include host or file, we'll take it from standard config instead
        file = config.file.text
    if not host:
        # print_overridable(Color.RED + 'Error: Episode is only available as HLS' + Color.END, True)
        filename = basepath + '.ts'
        print(Color.BOLD + 'File:       ' + Color.END + '{}'.format(filename))
        aes = None
        key = None
        url = config.file.text
        m3u8r = requests.get(url).text.splitlines()
        if len(m3u8r) < 10:
            url = random.choice(m3u8r[::2][1:])  # eases the burden on one server, makes it look less suspect
            m3u8r = requests.get(url).text.splitlines()
        urls = []
        for l in m3u8r:
            if l.startswith('#EXT-X-KEY:'):
                key, = re.findall('URI="([^"]+)', l)
                key = requests.get(key).content
                # print('Key: ' + hexlify(key).decode('ascii'))
                aes = AES.new(key, AES.MODE_CBC, b'\x00' * 16)
            elif l.startswith('#EXT-X-MEDIA-SEQUENCE:'):
                media_sequence, = re.findall('#EXT-X-MEDIA-SEQUENCE:(\d+)', l)
                aes = AES.new(key, AES.MODE_CBC, unhexlify('{:032x}'.format(int(media_sequence))))
            elif l.startswith('http'):
                urls.append(l)

        pbar = tqdm(total=len(urls), unit="seq")
        for u in urls:
            file = requests.get(u, stream=True)
            with open(filename, 'ab') as f:
                file.raw.decode_content = True
                for chunk in file:
                    f.write(aes.decrypt(chunk))
            pbar.update()
        pbar.close()

    else:
        filename = basepath + '.mp4'
        print(Color.BOLD + 'File:       ' + Color.END + '{}'.format(filename))
        print_overridable('Starting download...')
        if re.search('fplive\.net', host):
            url1, = re.findall('.+/c\d+', host)
            url2, = re.findall('c\d+\?.+', host)
        else:
            url1, = re.findall('.+/ondemand/', host)
            url2, = re.findall('ondemand/.+', host)
        proccommand = ['rtmpdump',
                       '-r', url1,
                       '-a', url2,
                       '-f', 'WIN 11,8,800,50',
                       '-m', '15',
                       '-W', 'http://www.crunchyroll.com/vendor/ChromelessPlayerApp-c0d121b.swf',
                       '-p', pageurl,
                       '-y', file,
                       '-o', filename]
        rtmpinfo = open(RTMP_INFO_TEMP_PATH, 'w+')
        proc = subprocess.Popen(proccommand,
                                stdin=subprocess.PIPE,
                                stdout=subprocess.DEVNULL,
                                stderr=rtmpinfo
                                )
        # TODO: Use file size instead of duration for the progress bar
        #       Need to obtain the total size
        pbar = tqdm(total=int(float(duration)), unit="sec")
        prev = 0
        while True:
            rtmpinfo.seek(0)
            for line in reversed(rtmpinfo.readlines()):
                if line.rstrip() == '':
                    continue
                r = re.search('([\d.]+) kB / ([\d.]+) sec', line)
                if r:
                    current = float(r.group(2))
                    pbar.update(int(current - prev))
                    prev = current
                    break
            rtmpinfo.seek(0)
            rtmpinfo.truncate()
            if proc.poll() is not None:
                break
        rtmpinfo.close()
        pbar.close()
        os.remove(RTMP_INFO_TEMP_PATH)
    print_under()
    print(Color.GREEN + 'Episode downloaded' + Color.END)

def download_series(series_id):
    resp = call_api('list_collections', {
        'series_id': series_id
    })
    if resp['error']:
        print(Color.RED + 'Error: Could not retrieve collections' + Color.END)
        return
    print(Color.BOLD + 'Collections:' + Color.END)
    for i, collection in enumerate(resp['data']):
        print((Color.BOLD + '{}:' + Color.END + ' {}').format(i+1, collection['name']))
    index = input('Which collection do you want to download (Specify a number)? ')
    if not index.isdigit():
        return # Did not specify a digit
    index = int(index) - 1
    if index >= len(resp['data']):
        return # Invalid number
    collection = resp['data'][index]
    resp = call_api('list_media', {
        'collection_id': collection['collection_id'],
        'fields': 'media.url,media.collection_name,media.name,media.episode_number,media.clip',
        'limit': 9999
    })
    if resp['error']:
        print(Color.RED + 'Error: Could not retrieve media' + Color.END)
        return
    for media in resp['data']:
        if media['clip']:
            print('"{} - {}" is a clip, skipping'.format(media['collection_name'], media['name']))
            continue
        basepath = DOWNLOAD_PATH.format(collection=safe_filename(media['collection_name']),
                                        media_name=safe_filename(media['name']),
                                        episode=int(media['episode_number'])
                                        )
        exists = False
        for fmt in ['mp4', 'ts']:
            if os.path.isfile(basepath + '.' + fmt):
                print('"' + basepath + '.' + fmt + '" already exists, skipping')
                break
        if not exists:
            download_media(media['url'])

def run_download(search):
    result = re.search('^https?:\/\/(?:www\.)?crunchyroll\.com\/', search)
    if result:
        # Check if it is a media URL
        result = re.search('^https?:\/\/(?:www\.)?crunchyroll\.com\/[^\/]+\/.*-[0-9]+\/?(\?|#|$)', search)
        if result:
            download_media(search)
            return
        # Check if it could be a series URL
        result = re.search('^https?:\/\/(?:www\.)?crunchyroll\.com\/[^\/]+\/?(\?|#|$)', search)
        if result:
            headers = {
                'Host': RPC_API_HOST,
                'User-Agent': USER_AGENT
            }
            print_overridable('Scraping page...')
            # Load page and look for div.show-actions[group_id] to obtain the series ID
            resp = requests.get(search, headers=headers, cookies={'sess_id': get_cache("session_id")})
            resp.encoding = 'utf-8'
            soup = BeautifulSoup(resp.text, 'html.parser')
            div = soup.find('div', class_='show-actions', attrs={'group_id': True})
            print_overridable()
            if div:
                download_series(div['group_id'])
                return
        # Catch remaining URLs
        print(Color.RED + 'Error: The specified URL was not for a series or media page' + Color.END)
        return

    if search is "":
        print(Color.RED + 'Error: Empty search query' + Color.END)
        return

    if not queue:
        update_queue()
        if not queue:
            return

    search = search.lower()
    series = None
    for item in queue:
        if search in item['series']['name'].lower():
            series = item['series']
            break
    if not series:
        print(Color.RED + 'Could not find any series' + Color.END)
        return
    if not input_yes('Found series \"{}\"\nDo you want to download it'.format(series['name'])):
        return
    download_series(series['series_id'])


def format_media_display(media):
    s = media['collection_name']
    ep = media['episode_number']
    if ep:  # Some media does not have an episode number
        s += " – E" + ep
    if media['name']:  # Episode might not have a name set
        if ep or media['name'] != media['collection_name']:
            # If no episode number is set, and both names are equal, it's likely a movie/special
            s += " – " + media['name']
    air = media['available_time']
    now = datetime.datetime.utcnow().replace(tzinfo=tz.tzutc())
    if air >= now:  # Show air time if episode hasn't aired yet
        s += " – " + air.strftime("%b %d %H:%M")
    return s


def show_queue(args=None):
    if args is None:
        args = []
    crnt_day = -1

    def following_title(airtime):
        nonlocal args
        nonlocal crnt_day
        if "following" in args:
            week_day = airtime.weekday()
            if week_day > crnt_day:
                crnt_day = week_day
                print('\n' + Color.BOLD + airtime.strftime("%A") + Color.END)

    if not queue or "update" in args:
        update_queue()
        if not queue:
            return

    if "following" in args:
        queue.sort(key=lambda e: e['most_likely_media']['available_time'].weekday())

    title = "All"
    if "following" in args:
        title = "Following"
    elif "watching" in args:
        title = "Watching"
    if "all" not in args:
        title += " (Unseen)"
    print(Color.BOLD + title + ':' + Color.END)
    now = datetime.datetime.utcnow().replace(tzinfo=tz.tzutc())
    count = 0
    for item in queue:
        media = item['most_likely_media']
        if ("watching" not in args and "following" not in args) or item['last_watched_media_playhead'] > 0:
            air = media['available_time']
            if not media['duration'] or air >= now:
                following_title(air)
                print(Color.YELLOW + format_media_display(media) + Color.END)
                count += 1
            else:
                seen = media['playhead'] >= media['duration'] * QUEUE_WATCHED_THRESHOLD
                if "all" in args or not seen:
                    days = math.ceil((now - air).total_seconds()) / 60 / 60 / 24
                    if "following" not in args or days < QUEUE_FOLLOWING_THRESHOLD:
                        following_title(air)
                        if seen:
                            print(Color.GREEN, end='')
                        print(format_media_display(media))
                        print(Color.END, end='')
                        count += 1
    print('')
    if count == 0:
        print(Color.RED + 'No series found' + Color.END)
    else:
        print((Color.GREEN + '{} series found' + Color.END).format(count))


def run_random(args):
    if not queue or "update" in args:
        update_queue()
        if not queue:
            return
    filtered = []
    for item in queue:
        if item['last_watched_media_playhead'] > 0:
            media = item['most_likely_media']
            if media['playhead'] < media['duration'] * QUEUE_WATCHED_THRESHOLD:
                filtered.append(media)
    run_media(random.choice(filtered)['url'])


def run_search(search):
    if search != "":
        if not queue:
            update_queue()
            if not queue:
                return

        print_overridable('Searching for \"{}\"...'.format(search))
        search = search.lower()
        media = None
        for item in queue:
            if search in item['series']['name'].lower():
                media = item['most_likely_media']
                break
        if media:
            print_overridable()
            if input_yes('Found \"{}\"\nDo you want to watch it'.format(format_media_display(media))):
                start_time = 0
                duration = media['duration']
                playhead = media['playhead']
                if 0 < playhead < duration and input_yes(
                        'Do you want to continue watching from {}/{}'.format(mmss(playhead), mmss(duration))):
                    start_time = playhead
                run_media(media['url'], start_time)
        else:
            print_overridable(Color.RED + 'Could not find any series' + Color.END, True)
    else:
        print(Color.RED + 'Error: Empty search query' + Color.END)


def show_help():
    print(
        Color.BOLD + 'Crunchyroll CLI Help' + Color.END + '\n\n' +
        Color.BOLD + 'URLs' + Color.END + '\n' +
        '       <episode url> [<start>]\n' +
        '         <start> determines how many seconds into the episode it should start.\n\n' +
        Color.BOLD + 'COMMANDS' + Color.END + '\n' +
        Color.BOLD + '       queue' + Color.END + ' [all] [following|watching] [update]\n' +
        '         Series where you\'ve seen past the watched threshold on the current episode are hidden unless "all" is provided.\n' +
        '         "watching" will filter out all series where you haven\'t began watching any episodes yet.\n' +
        '         "following" will filter out all series where an episode has been out for 2 weeks without you watching it.\n' +
        '         "update" will fetch the queue.\n' +
        Color.BOLD + '       watch' + Color.END + ' <search query>\n' +
        '         Search for a show in your queue and watch the episode you\'re currently on.\n' +
        Color.BOLD + '       download' + Color.END + ' [<series url>|<media url>|<search query>]\n' +
        '         Download an entire collection of a series by providing the series page URL.\n' +
        '         You can also specify the URL of media directly to download only that one.\n' +
        '         By providing a search query instead of a URL you can search for a series to download in your queue.\n' +
        Color.BOLD + '       prev' + Color.END + ' [resume|<start>]\n' +
        '         Watch the last media that was seen in the CLI.\n' +
        '         "resume" will continue the episode where it left off.\n' +
        '         <start> determines how many seconds into the episode it should start.\n' +
        Color.BOLD + '       rand' + Color.END + ' [update]\n' +
        '         Start watching a random episode from your queue.\n' +
        '         "update" will fetch the queue.\n' +
        Color.BOLD + '       exit' + Color.END + '\n'
    )


def main_loop(args=None):
    if args is None:
        args = []
    while True:
        if len(args) > 0:
            command = args[0].lower()
            if command == 'watch' or command == 'w':
                run_search(' '.join(args[1:]))
            elif command == 'download' or command == 'd':
                run_download(' '.join(args[1:]))
            elif command == 'queue' or command == 'q':
                show_queue(args[1:])
            elif command == 'auth' or command == 'a':
                authenticate(args[1:])
            elif command == 'rand' or command == 'r':
                run_random(args[1:])
            elif command == 'prev' or command == 'p':
                episode = get_cache('previous_episode')
                if episode:
                    playhead = 0
                    if len(args) > 1:
                        if args[1] == 'resume':
                            playhead = get_cache('previous_playhead')
                            if not playhead:
                                playhead = 0
                        else:
                            try:
                                playhead = int(args[1])
                            except ValueError:
                                pass
                    run_media(episode, playhead)
            elif command == 'exit':
                exit()
            elif command == 'help':
                show_help()
            elif re.search('^http(?:s)?://(?:[a-zA-Z]|\d|[$-_@.&+]|[!*(),]|(?:%[\w][\w]))+$', args[0]):
                if re.search(r'[\D](\d{6})(?:[\D]|$)', args[0]):
                    playhead = 0
                    if len(args) > 1:
                        try:
                            playhead = int(args[1])
                        except ValueError:
                            pass
                    run_media(args[0], playhead)
                else:
                    print(Color.RED + 'Error: Unknown url format' + Color.END)
            else:
                print(Color.RED + 'Error: Unknown command ' + command + Color.END)
        args = input('> ').split()


def exit_signal_handler(signum = None, frame = None):
    print()
    exit()


signal.signal(signal.SIGINT, exit_signal_handler)  # Remove traceback when exiting with ctrl+c
signal.signal(signal.SIGTSTP, exit_signal_handler)  # Remove stdout stuff when exiting with ctrl+z

print(Color.BOLD + 'Welcome to ' + Color.YELLOW + 'Crunchyroll CLI' + Color.END)
if len(argv) < 2 or argv[1].lower() != 'help':  # Do not print this message if they're already calling help
    print('Don\'t know what to do? Type "' + Color.BOLD + 'help' + Color.END + '"')
print()
if not (len(argv) > 1 and argv[1].lower() == 'auth') and AUTHENTICATE:
    # Do not authenticate here if the auth command is being called anyway
    authenticate([])
load_queue()
try:  # Remove traceback when exiting with ctrl+d
    main_loop(argv[1:])
except EOFError:
    exit_signal_handler()
