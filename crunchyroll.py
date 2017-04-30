#!/usr/bin/python3
import array
import base64
import datetime
import hashlib
import math
import os
import random
import re
import requests
import subprocess
import zlib
import signal
import time
import string
import getpass
import json

from dateutil import tz
from Crypto.Cipher import AES
from bs4 import BeautifulSoup
from sys import argv, exit, stdout

# Where should the cache file be stored?
# This file is used to store generated device id, session id, username and password
CACHE_PATH = os.path.dirname(os.path.realpath(__file__))+'/.crcache'
# Where should the subtitle file be stored?
SUBTITLE_TEMP_PATH = os.path.dirname(os.path.realpath(__file__))+'/.ass'

# How many days must pass before the show isn't considered followed
QUEUE_FOLLOWING_THRESHOLD = 14
# How many percentage of the video you must've seen for it to count as seen
QUEUE_WATCHED_THRESHOLD = 0.8
# Should it authenticate automatically on startup?
AUTHENTICATE = True

# END OF CONFIGURATION

API_HOST = 'api.crunchyroll.com'
RPC_API_HOST = 'www.crunchyroll.com'
USER_AGENT = 'Mozilla/5.0 (X11; Linux x86_64; rv:51.0) Gecko/20100101 Firefox/51.0'

queue = None
ram_cache = None

class color:
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
for i in dir(color):
    if not i.startswith("__"): colors[i] = getattr(color, i)

print_overridable_len = 0
#If string is empty, it ends override by cleaning up the current line
def print_overridable(str = '', end = False):
    global print_overridable_len
    old_len = print_overridable_len
    cleanstr = str
    for i,v in colors.items():
        cleanstr = cleanstr.replace(v, '')
    print_overridable_len = len(cleanstr)
    if old_len > print_overridable_len:
        str += ' '*(old_len-print_overridable_len)
    if end:
        print_overridable_len = 0
        print(str)
    else:
        print(str, end="\r", flush=True)

#End override by placing text on a new line
def print_under(str = ''):
    global print_overridable_len
    if len(str):
        print('\n'+str)
    else:
        print('')
    print_overridable_len = 0

def input_yes(question):
    answer = input(question+' (Y/N)? ')
    return answer.lower() == 'y'

def mmss(seconds):
    stamp = str(datetime.timedelta(seconds=int(float(seconds))))
    if stamp.startswith("0:"):
        stamp = stamp[2:]
    return stamp

def timestamp_to_datetime(ts):
    return (datetime.datetime.strptime(ts[:-7],'%Y-%m-%dT%H:%M:%S') + datetime.timedelta(hours=int(ts[-5:-3]), minutes=int(ts[-2:])) * -int(ts[-6:-5]+'1')).replace(tzinfo=tz.tzutc())

def call_api(name, params, secure = False):
    protocol = "http"
    if secure: protocol += "s"
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
    resp = requests.get('http://{}/xml/'.format(RPC_API_HOST), headers=headers, params=params, cookies={'sess_id': get_cache("session_id")})
    resp.encoding = 'utf-8'
    return resp

def generate_key(mediaid, size=32):
    # Below: Do some black magic
    eq1 = int(int(math.floor(math.sqrt(6.9) * math.pow(2, 25))) ^ mediaid)
    eq2 = int(math.floor(math.sqrt(6.9) * math.pow(2, 25)))
    eq3 = (mediaid ^ eq2) ^ (mediaid ^ eq2) >> 3 ^ eq1 * 32
    # Below: Creates a 160-bit SHA1 hash
    shaHash = hashlib.sha1()
    stringHash = create_string([20, 97, 1, 2]) + str(eq3)
    shaHash.update(stringHash.encode(encoding='UTF-8'))
    finalHash = shaHash.digest()
    hashArray = array.array('B', finalHash)
    # Below: Pads the 160-bit hash to 256-bit using zeroes, incase a 256-bit key is requested
    padding = [0]*4*3
    hashArray.extend(padding)
    keyArray = [0]*size
    # Below: Create a string of the requested key size
    for i, item in enumerate(hashArray[:size]):
        keyArray[i] = item
    return hashArray.tostring()

def create_string(args):
    i = 0
    argArray = [args[2], args[3]]
    while(i < args[0]):
        argArray.append(argArray[-1] + argArray[-2])
        i = i + 1
    finalString = ""
    for arg in argArray[2:]:
        finalString += chr(arg % args[1] + 33)
    return finalString

def decode_subtitles(id, iv, data):
    compressed = True
    key = generate_key(id)
    iv = base64.b64decode(iv)
    data = base64.b64decode(data)
    cipher = AES.new(key, AES.MODE_CBC, iv)
    decryptedData = cipher.decrypt(data)

    if compressed:
        return zlib.decompress(decryptedData)
    else:
        return decryptedData

def convert(script):
    soup = BeautifulSoup(script, 'xml')
    header = soup.find('subtitle_script')
    header = "[Script Info]\nTitle: "+header['title']+"\nScriptType: v4.00+\nWrapStyle: "+header['wrap_style']\
             + "\nPlayResX: "+header['play_res_x']+"\nPlayResY: "+header['play_res_y']+"\n\n"
    styles = "[V4+ Styles]\nFormat: Name, Fontname, Fontsize, PrimaryColour, SecondaryColour, OutlineColour, " \
             "BackColour, Bold, Italic, Underline, StrikeOut, ScaleX, ScaleY, Spacing, Angle, BorderStyle, " \
             "Outline, Shadow, Alignment, MarginL, MarginR, MarginV, Encoding\n"
    events = "\n[Events]\nFormat: Layer, Start, End, Style, Name, MarginL, MarginR, MarginV, Effect, Text\n"
    stylelist = soup.findAll('style')
    eventlist = soup.findAll('event')

    for style in stylelist:
        if style['scale_x'] or style['scale_y'] == '0':
            style['scale_x'], style['scale_y'] = '100', '100'  # Fix for Naruto 1-8 where it's set to 0 but ignored
        styles += "Style: " + style['name'] + "," + style['font_name'] + "," + style['font_size'] + ","\
                  + style['primary_colour'] + "," + style['secondary_colour'] + "," + style['outline_colour'] + ","\
                  + style['back_colour'] + "," + style['bold'] + "," + style['italic'] + ","\
                  + style['underline'] + "," + style['strikeout'] + "," + style['scale_x'] + ","\
                  + style['scale_y'] + "," + style['spacing'] + "," + style['angle'] + ","\
                  + style['border_style'] + "," + style['outline'] + "," + style['shadow'] + ","\
                  + style['alignment'] + "," + style['margin_l'] + "," + style['margin_r'] + ","\
                  + style['margin_v'] + "," + style['encoding'] + "\n"

    for event in eventlist:
        events += "Dialogue: 0,"+event['start']+","+event['end']+","+event['style']+","\
                  + event['name']+","+event['margin_l']+","+event['margin_r']+","+event['margin_v']\
                  + ","+event['effect']+","+event['text']+"\n"

    formattedsubs = header+styles+events
    return formattedsubs

def get_cache(key = None):
    def _get_cache():
        global ram_cache
        if ram_cache:
            return ram_cache
        if os.path.isfile(CACHE_PATH):
            with open(CACHE_PATH, 'r') as file:
                cache = file.read()
                if cache != "":
                    cache = json.loads(cache)
                    return cache
        return {}
    cache = _get_cache()
    if key != None:
        if key in cache:
            return cache[key]
        return None
    return cache

def set_cache(arg1, value = None):
    global ram_cache
    if value != None:
        cache = get_cache()
        cache[arg1] = value
    else:
        cache = arg1
    with open(CACHE_PATH, 'w+') as file:
        ram_cache = cache
        json.dump(cache, file)

def unset_cache(*keys):
    cache = get_cache()
    for key in keys:
        del cache[key]
    set_cache(cache)

def get_device_id():
    device_id = get_cache("device_id")
    if device_id != None: return device_id
    # Create a random device id and cache it
    char_set = string.ascii_letters + string.digits
    device_id = "".join(random.sample(char_set, 32))
    set_cache("device_id", device_id);
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
        print_overridable(color.RED+'Authentication has expired, must reauthenticate'+color.END, True)
    elif auth:
        data["auth"] = auth

    print_overridable('Creating session...')
    unset_cache('session_id') # The call will fail if you have an expired session set
    resp = call_api('start_session', data)

    if resp['error']:
        print_overridable(color.RED+'Error: '+resp['message']+color.END, True)
        return None
    else:
        print_overridable(color.GREEN+'Session created'+color.END, True)
        sess_id = resp['data']['session_id']
        if resp['data']['auth']:
            finish_auth(sess_id, resp['data']['auth'], resp['data']['expires'])
            return None #We return None to short-circuit the caller since the session is already authenticated
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
        print_overridable(color.RED+'Error: '+resp['message']+color.END, True)
    else:
        finish_auth(sess_id, resp['data']['auth'], resp['data']['expires'])

def finish_auth(sess_id, auth, expires):
    set_cache("auth", auth);
    set_cache("expires", timestamp_to_datetime(expires).timestamp());
    set_cache("session_id", sess_id);
    print_overridable(color.GREEN+'You are now authenticated'+color.END, True)

#TODO: Currently the session is dropped entirely if the authentication fails. We want to cache and re-use it on the next attempt!
def authenticate(args):
    global unassigned_session
    sess_id = get_cache("session_id");
    if sess_id and "new" not in args:
        resp = call_api('list_locales', {}) # This is just a dummy call used to determine if session is valid
        if not resp['error']:
            print(color.GREEN+'You are still authenticated'+color.END)
            return
        print(color.RED+'Session has expired'+color.END)
        unset_cache('session_id')

    sess_id = create_session()
    if sess_id:
        user = get_cache("user")
        if not user:
            user = input('Username: ')
            if input_yes("Remember username"):
                set_cache("user", user);
                print(color.GREEN+'Username saved'+color.END)
        password = get_cache("password")
        if not password:
            password = getpass.getpass()
            if input_yes("Remember password"):
                set_cache("password", password);
                print(color.GREEN+'Password saved'+color.END)
        authenticate_session(user, password, sess_id)

def update_queue():
    global queue
    if not get_cache("session_id"):
        if queue:
            print(color.YELLOW+'Error: Could not update queue. You are not authenticated'+color.END)
        else:
            print(color.RED+'Warning: Could not load queue. You are not authenticated'+color.END)
        return

    if queue:
        print_overridable('Updating queue...')
        resultStr = 'Queue updated'
    else:
        print_overridable('Loading queue...')
        resultStr = 'Queue loaded'
    data = {
        'fields': 'last_watched_media,last_watched_media_playhead,most_likely_media,most_likely_media_playhead,media.name,media.episode_number,media.available_time,media.duration,media.collection_name,media.url,series,series.name'
    }

    resp = call_api('queue', data)
    if resp['error']:
        if resp['code'] == "bad_session":
            msg = "Your session has expired. You are no longer authenticated"
            unset_cache("session_id")
        else:
            msg = "{} ({})".format(resp['message'], resp['code'])
        print_overridable(color.RED+'Error: Could not fetch queue. '+msg+color.END, True)
    else:
        queue = resp['data']
        for index, item in enumerate(queue):
            # Add missing integer values, and convert them from string to int
            for key in ['most_likely_media_playhead', 'last_watched_media_playhead']:
                val = item[key]
                if not val: val = 0
                else: val = int(val)
                queue[index][key] = val
            for media in ['most_likely_media', 'last_watched_media']:
                if not item[media]: continue
                for key in ['duration']:
                    val = item[media][key]
                    if not val: val = 0
                    else: val = int(val)
                    queue[index][media][key] = val
                queue[index][media]['available_time'] = timestamp_to_datetime(queue[index][media]['available_time'])

        print_overridable(color.GREEN+resultStr+color.END, True)

def run_media(pageurl, playhead = 0):
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
            print(color.RED+'Error: '+config.text+color.END)
            return

        #What is this even? Does it catch some specific media or 404 pages?
        if len(config.text) < 100:
            print(config.url)
            print(config.text)
            return

        config = BeautifulSoup(config.text, 'lxml-xml')

        #Check for errors
        error = config.find('error')
        if error:
            print(color.RED+'Error: '+error.msg.text+color.END)
            return

        #Check if media is unavailable
        error = config.find('upsell')
        if error:
            print(color.RED+'Error: Media is only available for premium members'+color.END)
            return

        nextEpisode = config.find('nextUrl').text
        series = config.series_title.text
        epnum = config.episode_number.text
        episode = config.episode_title.text
        duration = config.duration.text
        print('{} - E{}'.format(series, epnum))
        print(episode)
        print('Duration: {}'.format(mmss(duration)))

        sub = config.find('subtitle', attrs={'link': None})
        if sub:
            print_overridable('Preparing subtitles...')
            _id = int(sub['id'])
            _iv = sub.iv.text
            _subdata = sub.data.text
            # print(_id, _iv, _subdata)
            open(SUBTITLE_TEMP_PATH, 'w').write(convert(decode_subtitles(_id, _iv, _subdata).decode('utf-8')))

        print_overridable('Fetching stream information...')

        streamconfig = BeautifulSoup(call_rpc('RpcApiVideoEncode_GetStreamInfo', data).text, 'lxml-xml')
        streamconfig.encoding = 'utf-8'

        print_overridable('Starting stream...')
        if not streamconfig.host.text:
            # If by any chance that GetStreamInfo returns HLS, it should never get to this point
            url = streamconfig.file.text
            subarg = []
            if sub:
                subarg = ['--sub-file', SUBTITLE_TEMP_PATH]
            proccommand = ['mpv', url] + subarg

        else:
            host = streamconfig.host.text
            file = streamconfig.file.text
            if re.search('fplive\.net', host):
                url1, = re.findall('.+/c[0-9]+', host)
                url2, = re.findall('c[0-9]+\?.+', host)
            else:
                url1, = re.findall('.+/ondemand/', host)
                url2, = re.findall('ondemand/.+', host)

            subarg = ""
            if sub: subarg = " --sub-file '"+SUBTITLE_TEMP_PATH+"'"
            proccommand = "rtmpdump -a '"+url2+"' --flashVer 'WIN 11,8,800,50' -m 15 --pageUrl '"+pageurl+"' --rtmp '"+url1+"' --swfVfy http://www.crunchyroll.com/vendor/ChromelessPlayerApp-c0d121b.swf -y '"+file+"' --start "+str(playhead)+" | mpv --rebase-start-time=no --force-seekable=yes"+subarg+" -"

        proc = subprocess.Popen(
            proccommand,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
            bufsize=1,
            shell=True
        )

        # Pick up stderr for playhead and download information
        if playhead:
            startPosition = mmss(playhead)+'-'
        else:
            startPosition = ''
        downloadPosition = playhead
        while True:
            line = proc.stderr.readline().decode("utf-8")
            if line == '' and proc.poll() is not None:
                break
            download = re.search('([0-9.]+) kB / ([0-9.]+) sec', line)
            if download: downloadPosition = float(download.group(2))
            timestamp = re.search('V: ([0-9]{2}:[0-9]{2}:[0-9]{2}) / ([0-9]{2}:[0-9]{2}:[0-9]{2})', line)
            if timestamp:
                current = [int(i) for i in timestamp.group(1).split(":")]
                playhead = (current[0]*60+current[1])*60+current[2]
                if "Paused" in line:
                    paused = ' [PAUSED]'
                else:
                    paused = ''
                print_overridable((color.BOLD+'Playhead:'+color.END+' {}{} '+color.BOLD+'Downloaded:'+color.END+' {}{}').format(mmss(playhead), paused, startPosition, mmss(downloadPosition)))
        print_under()
        if sub: os.remove(SUBTITLE_TEMP_PATH)

        if get_cache("session_id") and input_yes('Do you want to update seen duration to {}/{}'.format(mmss(playhead), mmss(duration))):
            print_overridable('Updating seen duration...')
            resp = call_rpc('RpcApiVideo_VideoView', {
                'media_id': mediaid,
                'cbcallcount': 0,
                'cbelapsed': 30,
                'playhead': playhead
            })
            if resp.status_code != 200:
                print_overridable(color.RED+'Error: '+resp.text+color.END, True)
            else:
                print_overridable(color.GREEN+'Seen duration was saved'+color.END, True)
                update_queue() #We update the queue after marking episode as seen!

        if nextEpisode != "":
            if input_yes('Another episode is available, do you want to watch it'):
                pageurl = nextEpisode
                playhead = 0
            else:
                break
        else:
            print(color.RED+'No more episodes available'+color.END)
            break

def show_queue(args = []):
    crntDay = -1
    def following_title(air):
        nonlocal args
        nonlocal crntDay
        if "following" in args:
            localAir = air.astimezone(tz.tzlocal())
            weekDay = localAir.weekday()
            if weekDay > crntDay:
                crntDay = weekDay
                print('\n'+color.BOLD+localAir.strftime("%A")+color.END)

    if queue is None or "update" in args: update_queue()
    if queue is None: return

    items = list(queue)
    if "following" in args: items.sort(key=lambda e: e['most_likely_media']['available_time'].astimezone(tz.tzlocal()).weekday())

    title = "All"
    if "following" in args:
        title = "Following"
    elif "watching" in args:
        title = "Watching"
    if "all" not in args:
        title += " (Unseen)"
    print(color.BOLD+title+':'+color.END)
    now = datetime.datetime.utcnow().replace(tzinfo=tz.tzutc())
    count = 0
    for item in items:
        media = item['most_likely_media']
        if ("watching" not in args and "following" not in args) or item['last_watched_media_playhead'] > 0:
            air = media['available_time']
            seconds = math.ceil((now - air).total_seconds())
            duration = media['duration']
            if not duration:
                following_title(air)
                print((color.YELLOW+'{} - E{} - {}'+color.END).format(media['collection_name'], media['episode_number'], mmss(-seconds)))
                count += 1
            else:
                seen = item['most_likely_media_playhead'] >= duration * QUEUE_WATCHED_THRESHOLD
                if "all" in args or not seen:
                    days = seconds/60/60/24
                    if "following" not in args or days < QUEUE_FOLLOWING_THRESHOLD:
                        following_title(air)
                        if seen:
                            print(color.GREEN, end='')
                        print('{} - E{} - {}'.format(media['collection_name'], media['episode_number'], media['name']))
                        print(color.END, end='')
                        count += 1
    print('')
    if count == 0:
        print(color.RED+'No series found'+color.END)
    else:
        print((color.GREEN+'{} series found'+color.END).format(count))


def run_random(args):
    if queue is None or "update" in args: update_queue()
    if queue is None: return
    items = list(queue)
    filtered = []
    for item in items:
        media = item['most_likely_media']
        last_playhead = item['last_watched_media_playhead']
        if last_playhead > 0:
            if item['most_likely_media_playhead'] < media['duration'] * QUEUE_WATCHED_THRESHOLD:
                filtered.append(media)
    run_media(random.choice(filtered)['url'])

def run_search(search):
    if search != "":
        if queue is None:
            update_queue()
            if queue is None:
                return

        print_overridable('Searching for \"{}\"...'.format(search))
        search = search.lower()
        playhead = 0
        media = None
        for item in queue:
            if search in item['series']['name'].lower():
                playhead = item['most_likely_media_playhead']
                media = item['most_likely_media']
                break
        if media:
            print_overridable()
            if input_yes('Found \"{} - E{} - {}\"\nDo you want to watch it'.format(media['collection_name'], media['episode_number'], media['name'])):
                startTime = 0
                duration = media['duration']
                if playhead > 0 and playhead < duration and input_yes('Do you want to continue watching from {}/{}'.format(mmss(playhead), mmss(duration))):
                    startTime = playhead
                run_media(media['url'], startTime)
        else:
            print_overridable(color.RED+'Could not find any series'+color.END, True)
    else:
       print(color.RED+'Error: Empty search query'+color.END)

def show_help(args = []):
    print(
        color.BOLD+'Crunchyroll CLI Help'+color.END+'\n\n'+
        color.BOLD+'URL'+color.END+'\n'+
                   '       You can watch a specific episode by providing its crunchyroll.com URL.\n\n'+
        color.BOLD+'COMMANDS'+color.END+'\n'+
        color.BOLD+'       queue'+color.END+' [all] [following|watching] [update]\n'+
                   '         Series where you\'ve seen past the watched threshold on the current episode are hidden unless "all" is provided.\n'+
                   '         "watching" will filter out all series where you haven\'t began watching any episodes yet.\n'+
                   '         "following" will filter out all series where an episode has been out for 2 weeks without you watching it.\n'+
                   '         "update" will fetch the queue.\n'+
        color.BOLD+'       watch'+color.END+' <search query>\n'+
        color.BOLD+'       rand'+color.END+' [update]\n'+
        color.BOLD+'       exit'+color.END+'\n'
    )

def main_loop(args = []):
    while True:
        if len(args) > 0:
            command = args[0].lower()
            if command == 'watch' or command == 'w':
                run_search(' '.join(args[1:]))
            elif command == 'queue' or command == 'q':
                show_queue(args[1:])
            elif command == 'auth' or command == 'a':
                authenticate(args[1:])
            elif command == 'rand' or command == 'r':
                run_random(args[1:])
            elif command == 'exit':
                exit()
            elif command == 'help':
                show_help(args[1:])
            elif re.search('^http[s]?://(?:[a-zA-Z]|[0-9]|[$-_@.&+]|[!*\(\),]|(?:%[0-9a-fA-F][0-9a-fA-F]))+$', args[0]):
                if re.search(r'[^\d](\d{6})(?:[^\d]|$)', args[0]):
                    run_media(args[0])
                else:
                    print(color.RED+'Error: Unknown url format'+color.END)
            else:
                print(color.RED+'Error: Unknown command '+command+color.END)
        args = input('> ').split()


def exit_signal_handler(signal = None, frame = None):
    print('')
    exit()
signal.signal(signal.SIGINT, exit_signal_handler) #Remove traceback when exiting with ctrl+c
signal.signal(signal.SIGTSTP, exit_signal_handler) #Remove stdout stuff when exiting with ctrl+z

print(color.BOLD+'Welcome to '+color.YELLOW+'Crunchyroll CLI'+color.END)
if len(argv) < 2 or argv[1].lower() != 'help': #Do not print this message if they're already calling help
    print('Don\'t know what to do? Type "'+color.BOLD+'help'+color.END+'"')
print()
if not (len(argv) > 1 and argv[1].lower() == 'auth') and AUTHENTICATE: #Do not authenticate here if the auth command is being called anyway
    authenticate([])
try: #Remove traceback when exiting with ctrl+d
    main_loop(argv[1:])
except EOFError:
    exit_signal_handler()
