import discord
from discord.ext import commands, tasks
from discord import app_commands
import yt_dlp
import asyncio
import os
import shutil
import time
import requests
import sys
import logging
import datetime
import math
from typing import Dict, Any, List, Optional, Union
from bs4 import BeautifulSoup
from collections import deque
from config import LOG_CHANNEL_ID

# ----------------- SYSTEM LOGGING INFRASTRUCTURE -----------------
logging.basicConfig(level=logging.INFO, format="[%(asctime)s] [%(levelname)s] %(message)s")
logger = logging.getLogger("SpotifyStudioEngine")

def add_log(message: str):
    """Fallback logging adapter tracking cross-system exceptions."""
    logger.info(message)

# ----------------- ENVIRONMENTAL PERSISTENCE CONFIG -----------------
# Render deployment patterns enforce using /tmp space for file-system mutation write permissions
os.environ["TMPDIR"] = "/tmp"
STORAGE_ROOT = "/tmp/spotify_studio_cache"
os.makedirs(STORAGE_ROOT, exist_ok=True)

# ----------------- GLOBAL CONTEXT ARCHITECTURES -----------------
YT_DLP_CORE_OPTIONS = {
    "format": "bestaudio/best",
    "quiet": True,
    "noplaylist": True,
    "extract_flat": False,
    "source_address": "0.0.0.0",
    "default_search": "scsearch",
    "socket_timeout": 15,
    "retries": 10,
    "http_headers": {
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) "
            "Chrome/124.0.0.0 Safari/537.36"
        ),
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "en-us,en;q=0.5",
    }
}

# ----------------- DYNAMIC AUDIO FILTER MATRIX -----------------
class AudioFilterProfile:
    """Stores exact FFmpeg parameter injections for real-time equalizer manipulation."""
    DEFAULT = ""
    BASSBOOST = "-af equalizer=f=60:width_type=h:width=50:g=10"
    NIGHTCORE = "-af atempo=1.25,asetrate=44100*1.25"
    VAPORWAVE = "-af atempo=0.75,asetrate=44100*0.85"
    LOWPASS = "-af lowpass=f=1000"
    HIGHPASS = "-af highpass=f=2000"

# ----------------- ANTI-LAG FFMPEG CONFIG (EXPERT PROFILE) -----------------
FFMPEG_STREAMING_PROTOCOLS = {
    "before_options": (
        "-reconnect 1 "
        "-reconnect_streamed 1 "
        "-reconnect_delay_max 5 "
        "-listen_timeout 10000000 "
        "-threads 2 "
        "-nostats "
        "-loglevel panic"
    ),
    "options": (
        "-vn "
        "-b:a 192k "
        "-bufsize 4096k "
        "-probesize 32 "
    )
}

# ----------------- MEMORY CACHE REGISTRY -----------------
class TrackCacheManager:
    """Manages structural tracking maps of downloaded binary data streams to prevent memory leaks."""
    def __init__(self):
        self._registry: Dict[str, Dict[str, Any]] = {}
        self._max_cache_size = 50

    def register_track(self, track_id: str, payload: Dict[str, Any]):
        if len(self._registry) >= self._max_cache_size:
            oldest = min(self._registry.keys(), key=lambda k: self._registry[k].get("timestamp", 0))
            self.purge_track(oldest)
        payload["timestamp"] = time.time()
        self._registry[track_id] = payload

    def get_track(self, track_id: str) -> Optional[Dict[str, Any]]:
        if track_id in self._registry:
            self._registry[track_id]["timestamp"] = time.time()
            return self._registry[track_id]
        return None

    def purge_track(self, track_id: str):
        if track_id in self._registry:
            file_path = self._registry[track_id].get("local_path")
            if file_path and os.path.exists(file_path):
                try:
                    os.remove(file_path)
                except Exception as e:
                    add_log(f"Cache file purge error: {e}")
            del self._registry[track_id]

    def clear_all(self):
        for track_id in list(self._registry.keys()):
            self.purge_track(track_id)

cache_manager = TrackCacheManager()

# ----------------- GUILD TRANSACTION STATE TREE -----------------
class GuildState:
    """Tracks independent streaming channels, volumes, queues, and presentation views per Guild ID."""
    def __init__(self, guild_id: int):
        self.guild_id: int = guild_id
        self.queue: deque = deque()
        self.history: List[Dict[str, Any]] = []
        self.current: Optional[Dict[str, Any]] = None
        self.loop: bool = False
        self.queue_loop: bool = False
        self.volume: float = 0.5
        self.text_channel: Optional[discord.TextChannel] = None
        self.is_loading: bool = False
        self.last_activity: float = time.time()
        self.controller_msg: Optional[discord.Message] = None
        self.track_start_time: float = 0.0
        self.paused_duration: float = 0.0
        self.pause_start_time: float = 0.0
        self.active_filter: str = AudioFilterProfile.DEFAULT
        self.requester_map: Dict[str, discord.Member] = {}
        self.switching_filter: bool = False
        self.seek_offset: float = 0.0

    def reset_track_clocks(self):
        self.track_start_time = time.time()
        self.paused_duration = 0.0
        self.pause_start_time = 0.0

    def clear(self):
        self.queue.clear()
        self.current = None
        self.loop = False
        self.queue_loop = False
        self.active_filter = AudioFilterProfile.DEFAULT
        self.switching_filter = False
        self.seek_offset = 0.0


# ----------------- PREMIUM UI COMPONENT LAYOUTS -----------------
class SpotifyController(discord.ui.View):
    """Interactive visual button row tracking media loop pipelines."""
    def __init__(self, cog, guild_id: int):
        super().__init__(timeout=None)
        self.cog = cog
        self.guild_id: int = guild_id
    def update_buttons(self, state: GuildState):
        for child in self.children:
            if not isinstance(child, discord.ui.Button):
                continue
            if child.custom_id == "loop_toggle":
                if state.loop:
                    child.style = discord.ButtonStyle.success
                    child.label = "🔁 Loop: Track"
                elif state.queue_loop:
                    child.style = discord.ButtonStyle.success
                    child.label = "🔁 Loop: Queue"
                else:
                    child.style = discord.ButtonStyle.secondary
                    child.label = "🔁 Repeat"
            elif child.custom_id == "play_pause":
                vc = self.cog.bot.get_guild(self.guild_id).voice_client
                child.label = "▶ Resume" if vc and vc.is_paused() else "⏸ Pause"
                child.style = discord.ButtonStyle.success if vc and not vc.is_paused() else discord.ButtonStyle.primary

    # ROW 1: PRIMARY PLAYBACK CONTROLS
    @discord.ui.button(label="⏪ -10s", style=discord.ButtonStyle.secondary, custom_id="seek_back", row=1)
    async def seek_back(self, interaction: discord.Interaction, button: discord.ui.Button):
        vc = interaction.guild.voice_client
        state = self.cog.get_state(interaction.guild.id)
        if not vc or not vc.is_playing() or not state.current:
            return await interaction.response.send_message("❌ Nothing is actively playing to seek.", ephemeral=True)
        
        state.track_start_time += 10
        vc.stop()
        await interaction.response.send_message("⏪ Seeked backward 10 seconds.", ephemeral=True)

    @discord.ui.button(label="⏸ Pause", style=discord.ButtonStyle.primary, custom_id="play_pause", row=1)
    async def play_pause(self, interaction: discord.Interaction, button: discord.ui.Button):
        vc = interaction.guild.voice_client
        state = self.cog.get_state(interaction.guild.id)
        if not vc:
            return await interaction.response.send_message("❌ Voice connection missing.", ephemeral=True)

        if vc.is_playing():
            vc.pause()
            state.pause_start_time = time.time()

            button.label = "▶ Resume"
            button.style = discord.ButtonStyle.success

            action = "Paused"
            color = discord.Color.yellow()

        elif vc.is_paused():
            vc.resume()
            state.paused_duration += time.time() - state.pause_start_time

            button.label = "⏸ Pause"
            button.style = discord.ButtonStyle.primary

            action = "Resumed"
            color = discord.Color.green()

        embed = discord.Embed(
            title=f"⏸ Stream {action}" if action == "Paused" else f"▶ Stream {action}",
            description=(
                f"**User:** {interaction.user.mention} (`{interaction.user.id}`)\n"
                f"**Action:** Music Control Panel"
            ),
            color=color
        )
        embed.timestamp = datetime.datetime.now(datetime.timezone.utc)

        await self.cog.send_log(interaction, embed)

        self.update_buttons(state)
        await interaction.response.edit_message(view=self)
    @discord.ui.button(label="⏩ +10s", style=discord.ButtonStyle.secondary, custom_id="seek_forward", row=1)
    async def seek_forward(self, interaction: discord.Interaction, button: discord.ui.Button):
        vc = interaction.guild.voice_client
        state = self.cog.get_state(interaction.guild.id)
        if not vc or not vc.is_playing() or not state.current:
            return await interaction.response.send_message("❌ Nothing is actively playing to seek.", ephemeral=True)
        
        state.track_start_time -= 10
        vc.stop()
        await interaction.response.send_message("⏩ Seeked forward 10 seconds.", ephemeral=True)

    # ROW 2: UTILITY CONTROLS
    @discord.ui.button(label="🔁 Repeat", style=discord.ButtonStyle.secondary, custom_id="loop_toggle", row=2)
    async def loop_toggle(self, interaction: discord.Interaction, button: discord.ui.Button):
        state = self.cog.get_state(interaction.guild.id)
        if not state.loop and not state.queue_loop:
            state.loop = True
            state.queue_loop = False
        elif state.loop:
            state.loop = False
            state.queue_loop = True
        else:
            state.loop = False
            state.queue_loop = False

        self.update_buttons(state)
        await interaction.response.edit_message(view=self)

    @discord.ui.button(label="⏭ Skip", style=discord.ButtonStyle.danger, custom_id="skip_track", row=2)
    async def skip_track(self, interaction: discord.Interaction, button: discord.ui.Button):
        vc = interaction.guild.voice_client

        if vc and (vc.is_playing() or vc.is_paused()):
            state = self.cog.get_state(interaction.guild.id)

            was_looping = state.loop
            state.loop = False

            vc.stop()

            state.loop = was_looping

            embed = discord.Embed(
                title="⏭ Track Skipped",
                description=(
                    f"**User:** {interaction.user.mention} (`{interaction.user.id}`)\n"
                    f"**Action:** Music Control Panel"
                ),
                color=discord.Color.orange()
            )
            embed.timestamp = datetime.datetime.now(datetime.timezone.utc)

            try:
                log_channel = interaction.client.get_channel(LOG_CHANNEL_ID)

                if not log_channel:
                    log_channel = await interaction.client.fetch_channel(LOG_CHANNEL_ID)

                await log_channel.send(embed=embed)

            except Exception as e:
                logger.error(f"Failed to send skip log: {e}")

            await interaction.response.send_message(
                "⏭ Track skip call executed.",
                ephemeral=True
            )

        else:
            await interaction.response.send_message(
                "❌ No track currently active.",
                ephemeral=True
            )

class SpotifyFilterMenu(discord.ui.Select):
    """Drop-down menu layout allowing live filter profile transformations."""
    def __init__(self, cog, guild_id: int):
        self.cog = cog
        self.guild_id = guild_id
        options = [
            discord.SelectOption(label="Standard Audio", value="default", description="Clear bypass audio settings."),
            discord.SelectOption(label="Bass Boost", value="bassboost", description="Amplify sub-woofer low end frequencies."),
            discord.SelectOption(label="Nightcore", value="nightcore", description="Accelerate pitch and timestamp speed arrays."),
            discord.SelectOption(label="Vaporwave", value="vaporwave", description="De-accelerate track tempo elements."),
            discord.SelectOption(label="Lowpass Filter", value="lowpass", description="Muffle upper tier vocal arrays."),
            discord.SelectOption(label="Highpass Filter", value="highpass", description="Isolate high frequency instrumental transients.")
        ]
        super().__init__(placeholder="🎛 Choose Live DSP Equalizer Profile...", min_values=1, max_values=1, options=options, custom_id="dsp_select", row=0)

    async def callback(self, interaction: discord.Interaction):
        state = self.cog.get_state(self.guild_id)
        vc = interaction.guild.voice_client
        selection = self.values[0]

        if not vc or not state.current:
            return await interaction.response.send_message("❌ Nothing is playing right now.", ephemeral=True)

        if selection == "default": state.active_filter = AudioFilterProfile.DEFAULT
        elif selection == "bassboost": state.active_filter = AudioFilterProfile.BASSBOOST
        elif selection == "nightcore": state.active_filter = AudioFilterProfile.NIGHTCORE
        elif selection == "vaporwave": state.active_filter = AudioFilterProfile.VAPORWAVE
        elif selection == "lowpass": state.active_filter = AudioFilterProfile.LOWPASS
        elif selection == "highpass": state.active_filter = AudioFilterProfile.HIGHPASS

        state.switching_filter = True
        
        if vc.is_playing():
            elapsed = time.time() - state.track_start_time - state.paused_duration
        else:
            elapsed = state.pause_start_time - state.track_start_time - state.paused_duration
            
        state.seek_offset = max(0.0, elapsed)

        await interaction.response.send_message(f"🎛 Processing DSP EQ Matrix Profile: `{selection.upper()}`...", ephemeral=True)
        vc.stop()


class SpotifyUIPackage(discord.ui.View):
    """Parent UI composite linking interactive button collections and drop-down menu layouts."""
    def __init__(self, cog, guild_id: int):
        super().__init__(timeout=None)
        self.cog = cog
        self.guild_id = guild_id
        
        self.add_item(SpotifyFilterMenu(cog, guild_id))
        controller = SpotifyController(cog, guild_id)
        for child in list(controller.children):
            self.add_item(child)

    def update_all_components(self, state: GuildState):
        for child in self.children:
            if isinstance(child, discord.ui.Button):
                if child.custom_id == "loop_toggle":
                    if state.loop:
                        child.style = discord.ButtonStyle.success
                        child.label = "🔁 Loop: Track"
                    elif state.queue_loop:
                        child.style = discord.ButtonStyle.success
                        child.label = "🔁 Loop: Queue"
                    else:
                        child.style = discord.ButtonStyle.secondary
                        child.label = "🔁 Repeat"
                elif child.custom_id == "play_pause":
                    vc = self.cog.bot.get_guild(self.guild_id).voice_client
                    child.label = "▶ Resume" if vc and vc.is_paused() else "⏸ Pause"
                    child.style = discord.ButtonStyle.success if vc and not vc.is_paused() else discord.ButtonStyle.primary

# ----------------- COMPONENT MUSIC COG SYSTEM -----------------
class Music(commands.Cog):
    def __init__(self, bot: commands.Bot):
        self.bot = bot
        self.states: Dict[int, GuildState] = {}
        self.ui_updater_loop.start()
        self.session_garbage_collection.start()
    async def send_log(self, interaction: discord.Interaction, embed: discord.Embed):
        try:
            logger.info(f"LOG_CHANNEL_ID = {LOG_CHANNEL_ID}")

            log_channel = interaction.client.get_channel(LOG_CHANNEL_ID)

            if log_channel is None:
                logger.error("Log channel not found in cache.")
                log_channel = await interaction.client.fetch_channel(LOG_CHANNEL_ID)

            logger.info(f"Found log channel: {log_channel}")

            await log_channel.send(embed=embed)

        except Exception as e:
            logger.exception(f"Logging failed: {e}")
    def cog_unload(self):
        self.ui_updater_loop.cancel()
        self.session_garbage_collection.cancel()
        cache_manager.clear_all()

    def get_state(self, guild_id: int) -> GuildState:
        if guild_id not in self.states:
            self.states[guild_id] = GuildState(guild_id)
        return self.states[guild_id]

    def format_time(self, seconds: float) -> str:
        if math.isnan(seconds) or math.isinf(seconds):
            return "00:00"
        mins, secs = divmod(int(seconds), 60)
        return f"{mins:02d}:{secs:02d}"

    def generate_bar(self, current: float, total: float) -> str:
        if total <= 0:
            return "⬛" * 15
        percent = current / total
        progress = int(percent * 15)
        progress = max(0, min(progress, 15))
        return "🟩" * progress + "⬛" * (15 - progress)

    # ----------------- TIMELINE PROGRESS ENGINE LOOP -----------------
    @tasks.loop(seconds=6.0)
    async def ui_updater_loop(self):
        for guild_id, state in list(self.states.items()):
            guild = self.bot.get_guild(guild_id)
            if not guild:
                continue
            vc = guild.voice_client
            if not vc or not state.current or not state.controller_msg:
                continue

            if vc.is_playing() or vc.is_paused():
                try:
                    if vc.is_playing():
                        elapsed = time.time() - state.track_start_time - state.paused_duration
                    else:
                        elapsed = state.pause_start_time - state.track_start_time - state.paused_duration

                    duration = state.current.get("duration", 0)
                    if not duration:
                        continue

                    elapsed = max(0.0, min(elapsed, float(duration)))
                    bar_str = self.generate_bar(elapsed, duration)
                    time_stamp = f"`{self.format_time(elapsed)}` 🔘 {bar_str} `{self.format_time(duration)}`"

                    embed = state.controller_msg.embeds[0]
                    embed.set_field_at(2, name="Timeline Position", value=time_stamp, inline=False)
                    
                    await state.controller_msg.edit(embed=embed)
                except discord.errors.NotFound:
                    state.controller_msg = None
                except Exception as e:
                    add_log(f"UI refresh exception: {e}")

    @ui_updater_loop.before_loop
    async def before_ui_updater(self):
        await self.bot.wait_until_ready()

    # ----------------- SECURITY CLEANUP GARBAGE COLLECTOR -----------------
    @tasks.loop(minutes=5.0)
    async def session_garbage_collection(self):
        now = time.time()
        for guild_id, state in list(self.states.items()):
            guild = self.bot.get_guild(guild_id)
            if not guild:
                continue
            vc = guild.voice_client
            if vc:
                members = vc.channel.members
                if len(members) == 1 and (now - state.last_activity) > 180:
                    state.clear()
                    if state.text_channel:
                        try:
                            embed = discord.Embed(description="💤 Channel empty, disconnecting.", color=0x010101)
                            await state.text_channel.send(embed=embed)
                        except Exception: pass
                    await vc.disconnect()
            else:
                if (now - state.last_activity) > 600:
                    del self.states[guild_id]

    # ----------------- SOUNDCLOUD DATA FETCHERS -----------------
    async def get_soundcloud_playlist(self, url: str) -> List[Dict[str, Any]]:
        loop = asyncio.get_event_loop()
        def extract():
            with yt_dlp.YoutubeDL(YT_DLP_CORE_OPTIONS) as ydl:
                return ydl.extract_info(url, download=False)
        
        try:
            data = await loop.run_in_executor(None, extract)
            if not data or "entries" not in data:
                return []
            
            playlist = []
            for entry in data["entries"]:
                if not entry:
                    continue
                playlist.append({
                    "title": entry.get("title", "Unknown Track"),
                    "url": entry.get("url") or entry.get("webpage_url"),
                    "uploader": entry.get("uploader", "Unknown Artist"),
                    "thumbnail": entry.get("thumbnail", "https://i.imgur.com/7SgVwS4.png"),
                    "duration": entry.get("duration", 180)
                })
            return playlist
        except Exception as e:
            add_log(f"Playlist track parse exception: {e}")
            return []

    async def search_soundcloud(self, query: str) -> str:
        url = f"https://soundcloud.com/search?q={requests.utils.quote(query)}"
        headers = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"}
        
        loop = asyncio.get_event_loop()
        def fetch():
            return requests.get(url, headers=headers, timeout=10)
            
        response = await loop.run_in_executor(None, fetch)
        if response.status_code != 200:
            raise Exception(f"SoundCloud indexing network connection failure: {response.status_code}")

        soup = BeautifulSoup(response.text, "html.parser")
        links = soup.find_all("a")

        for link in links:
            href = link.get("href")
            if href and href.startswith("/") and "/search" not in href and href.count("/") >= 2:
                if not any(x in href for x in ["/terms-of-use", "/pages/", "/popular/"]):
                    return f"https://soundcloud.com{href}"

        raise Exception("❌ No matching track discovered matching search descriptors.")

    async def search_song(self, query: str) -> Dict[str, Any]:
        loop = asyncio.get_event_loop()
        def extract():
            with yt_dlp.YoutubeDL(YT_DLP_CORE_OPTIONS) as ydl:
                return ydl.extract_info(query, download=False)

        data = await loop.run_in_executor(None, extract)
        if not data:
            raise Exception("Parsing matrix returned an empty dataset payload layout.")

        if "entries" in data:
            entries = data.get("entries")
            if not entries:
                raise Exception("Zero array indexes discovered inside stream container mappings.")
            data = entries[0]
        
        stream_url = data.get("url")
        if not stream_url:
            formats = data.get("formats", [])
            for f in formats:
                if f.get("acodec") != "none" and f.get("url"):
                    stream_url = f["url"]
                    break

        if not stream_url:
            raise Exception("Asset allocation extraction verification target failure.")

        return {
            "title": data.get("title", "Unknown Track"),
            "url": stream_url,
            "webpage_url": data.get("webpage_url", query),
            "uploader": data.get("uploader", "Independent Artist Profile"),
            "thumbnail": data.get("thumbnail") or "https://i.imgur.com/7SgVwS4.png",
            "duration": int(data.get("duration", 180))
        }

    # ----------------- APPLICATION ENTRY LAYER COMMANDS -----------------
    @app_commands.command(name="join", description="Connect to your active voice channel safely.")
    async def join(self, interaction: discord.Interaction):
        if not interaction.user.voice:
            return await interaction.response.send_message("❌ Connect to a voice channel before running this command.", ephemeral=True)

        channel = interaction.user.voice.channel
        vc = interaction.guild.voice_client

        if vc:
            if vc.channel.id == channel.id:
                return await interaction.response.send_message("ℹ Already actively routing audio inside that matching layout.", ephemeral=True)
            await vc.move_to(channel)
        else:
            await channel.connect()

        state = self.get_state(interaction.guild.id)
        state.text_channel = interaction.channel
        state.last_activity = time.time()

        embed = discord.Embed(description=f"🎧 Linked safely to destination target channel: {channel.mention}", color=0x010101)
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="play", description="Stream audio smoothly across alternative platform configurations.")
    async def play(self, interaction: discord.Interaction, query: str):
        await interaction.response.defer()
        state = self.get_state(interaction.guild.id)
        state.text_channel = interaction.channel
        state.last_activity = time.time()
        vc = interaction.guild.voice_client

        if not vc:
            if not interaction.user.voice:
                return await interaction.followup.send("❌ Join a target voice execution pipeline layer first.")
            vc = await interaction.user.voice.channel.connect()

        if "youtube.com" in query or "youtu.be" in query:
            return await interaction.followup.send("❌ Corporate API distribution locks restrict native YouTube streaming.")

        try:
            if "soundcloud.com" in query and "/sets/" in query:
                tracks = await self.get_soundcloud_playlist(query)
                if not tracks:
                    return await interaction.followup.send("❌ Target playlist payload container was empty or unreadable.")
                
                for t in tracks:
                    state.queue.append(t)
                
                embed = discord.Embed(title="CLOUT SYSTEM PLAYLIST ENGINE BUNDLE INSTALLED", color=0x010101)
                embed.add_field(name="Processing Totals", value=f"Added **{len(tracks)}** elements cleanly into systemic tracks.", inline=False)
                await interaction.followup.send(embed=embed)
                
                if not (vc.is_playing() or vc.is_paused() or state.is_loading):
                    await self.play_next(vc, state)
                return

            if "soundcloud.com" not in query:
                query = await self.search_soundcloud(query)

            song = await self.search_song(query)
        except Exception as e:
            add_log(f"Extraction track tracing exception layout: {e}")
            return await interaction.followup.send(f"❌ Structural ingestion tracking error: ```{e}```")

        state.queue.append(song)
        
        embed = discord.Embed(title="ADDED TO PIPELINE TRACK QUEUE", color=0x010101)
        embed.add_field(name="Element Identity", value=f"```⚡ {song['title']}```", inline=False)
        await interaction.followup.send(embed=embed)

        if not (vc.is_playing() or vc.is_paused() or state.is_loading):
            await self.play_next(vc, state)

    @app_commands.command(name="playfile", description="Upload and play a direct audio file (.mp3, .wav)")
    async def playfile(self, interaction: discord.Interaction, file: discord.Attachment):
        await interaction.response.defer()
        if not file.filename.lower().endswith(('.mp3', '.wav', '.m4a', '.ogg', '.flac')):
            return await interaction.followup.send("❌ Incompatible format standard array mapping configurations supplied.")

        state = self.get_state(interaction.guild.id)
        state.text_channel = interaction.channel
        state.last_activity = time.time()
        vc = interaction.guild.voice_client

        if not vc:
            if not interaction.user.voice:
                return await interaction.followup.send("❌ Connection routing paths are missing active destination channels.")
            vc = await interaction.user.voice.channel.connect()

        local_filename = f"{int(time.time())}_{file.filename}"
        local_path = os.path.join(STORAGE_ROOT, local_filename)

        try:
            await file.save(local_path)
        except Exception as e:
            return await interaction.followup.send(f"❌ Attachment write pipeline error: {e}")

        song = {
            "title": file.filename,
            "url": local_path,
            "webpage_url": "https://discord.com",
            "uploader": "Direct Local System Upload Asset File",
            "thumbnail": "https://i.imgur.com/7SgVwS4.png",
            "duration": 200
        }

        state.queue.append(song)
        await interaction.followup.send(f"📁 Local file system binary array asset cached safely inside temporary system directory.")

        if not (vc.is_playing() or vc.is_paused() or state.is_loading):
            await self.play_next(vc, state)

    # ----------------- SYSTEM AUDIO TRANSMISSION ENGINE -----------------
    async def play_next(self, vc: discord.VoiceClient, state: GuildState):
        state.is_loading = True
        is_rebuilding = getattr(state, 'switching_filter', False)
        
        if is_rebuilding and state.current:
            song = state.current
            state.switching_filter = False
        elif state.loop and state.current:
            song = state.current
        elif not state.queue:
            state.current = None
            state.is_loading = False
            if state.controller_msg:
                try: await state.controller_msg.delete()
                except Exception: pass
                state.controller_msg = None
            return
        else:
            if state.queue_loop and state.current:
                state.queue.append(state.current)
            song = state.queue.popleft()

        if state.current and state.current not in state.history:
            state.history.append(state.current)
            if len(state.history) > 25:
                state.history.pop(0)

        state.current = song
        
        if not is_rebuilding:
            state.track_start_time = time.time()
            state.paused_duration = 0.0
            state.pause_start_time = 0.0
            seek_time_param = 0.0
        else:
            seek_time_param = getattr(state, 'seek_offset', 0.0)
            state.track_start_time = time.time() - seek_time_param
            state.paused_duration = 0.0

        state.is_loading = False
        state.last_activity = time.time()
        ffmpeg_path = shutil.which("ffmpeg") or "ffmpeg"
        
        if song["url"].startswith("http"):
            integrated_before_opts = ""
            if seek_time_param > 0:
                integrated_before_opts += f"-ss {seek_time_param:.2f} "
            integrated_before_opts += FFMPEG_STREAMING_PROTOCOLS["before_options"]
            integrated_opts = FFMPEG_STREAMING_PROTOCOLS["options"]
        else:
            integrated_before_opts = ""
            if seek_time_param > 0:
                integrated_before_opts += f"-ss {seek_time_param:.2f} "
            integrated_before_opts += "-threads 2 -nostats -loglevel panic"
            integrated_opts = "-vn -b:a 192k -bufsize 4096k"

        if state.active_filter != AudioFilterProfile.DEFAULT:
            integrated_opts += " " + state.active_filter

        def after_handler(error):
            if error:
                print(f"CORE EXECUTION ENGINE ERROR: {error}")
            
            is_rebuilding_callback = getattr(state, 'switching_filter', False)
            if not is_rebuilding_callback and song["url"].startswith(STORAGE_ROOT) and os.path.exists(song["url"]):
                if not state.loop:
                    try: os.remove(song["url"])
                    except Exception: pass

            asyncio.run_coroutine_threadsafe(self.play_next(vc, state), self.bot.loop)

        try:
            source = discord.FFmpegPCMAudio(
                song["url"],
                executable=ffmpeg_path,
                before_options=integrated_before_opts,
                options=integrated_opts
            )
            
            transformed_source = discord.PCMVolumeTransformer(source, volume=state.volume)
            vc.play(transformed_source, after=after_handler)

            if state.text_channel:
                embed = discord.Embed(title="CLOUT MUSIC INTERFACE INITIALIZED", color=0x010101)
                embed.set_thumbnail(url=song.get("thumbnail", "https://i.imgur.com/7SgVwS4.png"))
                embed.add_field(name="Track Title Name", value=f"{song['title']}", inline=False)
                embed.add_field(name="Artist Profile Channel", value=f"{song['uploader']}", inline=True)
                
                filter_label = "STANDARD BYPASS CONTROL" if state.active_filter == AudioFilterProfile.DEFAULT else "ACTIVE DSP EQUALIZER MATRIX"
                embed.add_field(name="DSP Signal Processing Mode", value=f"{filter_label}", inline=True)
                
                elapsed_display = seek_time_param if seek_time_param > 0 else 0.0
                bar_str = self.generate_bar(elapsed_display, song["duration"])
                embed.add_field(name="Timeline Position", value=f"`{self.format_time(elapsed_display)}` 🔘 {bar_str} {self.format_time(song['duration'])}", inline=False)
                embed.set_footer(text="Clout's Music UI • Premium Layout Active", icon_url="https://i.imgur.com/7SgVwS4.png")

                view = SpotifyUIPackage(self, state.text_channel.guild.id)
                view.update_all_components(state)

                if state.controller_msg and not is_rebuilding:
                    try: await state.controller_msg.delete()
                    except Exception: pass
                    state.controller_msg = await state.text_channel.send(embed=embed, view=view)
                elif state.controller_msg and is_rebuilding:
                    await state.controller_msg.edit(embed=embed, view=view)
                else:
                    state.controller_msg = await state.text_channel.send(embed=embed, view=view)

        except Exception as e:
            add_log(f"Media streaming connection crash tracking failure: {e}")
            state.is_loading = False
            state.switching_filter = False
            asyncio.run_coroutine_threadsafe(self.play_next(vc, state), self.bot.loop)

    # ----------------- SYSTEM USER CONTROL COMMAND ARRAYS -----------------
    @app_commands.command(name="skip", description="Skip the current track.")
    async def skip(self, interaction: discord.Interaction):
        vc = interaction.guild.voice_client
        if not vc or not (vc.is_playing() or vc.is_paused()):
            return await interaction.response.send_message("❌ System signals reflect a dormant track core status.", ephemeral=True)
        
        state = self.get_state(interaction.guild.id)
        state.loop = False
        vc.stop()
        embed = discord.Embed(
            title="⏭ Track Skipped",
            description=(
                f"**User:** {interaction.user.mention} (`{interaction.user.id}`)\n"
                f"**Channel:** {interaction.user.voice.channel.mention if interaction.user.voice else 'Unknown'}"
            ),
            color=discord.Color.orange()
        )
        embed.timestamp = datetime.datetime.now(datetime.timezone.utc)

        await self.send_log(interaction, embed)
        await interaction.response.send_message("⏭ Skip sequencing array executed successfully.")

    @app_commands.command(name="pause", description="Halt operational ongoing stream pipelines.")
    async def pause(self, interaction: discord.Interaction):
        vc = interaction.guild.voice_client
        if not vc or not vc.is_playing():
            return await interaction.response.send_message("❌ Track is either already suspended or inactive.", ephemeral=True)
        
        state = self.get_state(interaction.guild.id)
        vc.pause()
        state.pause_start_time = time.time()

        embed = discord.Embed(
            title="⏸ Stream Paused",
            description=(
                f"**User:** {interaction.user.mention} (`{interaction.user.id}`)\n"
                f"**Action:** Command Pipeline Pause"
            ),
            color=discord.Color.yellow()
        )
        embed.timestamp = datetime.datetime.now(datetime.timezone.utc)

        await self.send_log(interaction, embed)
        await interaction.response.send_message("⏸ Audio translation paused.")

    @app_commands.command(name="resume", description="Re-engage halted streaming pipelines.")
    async def resume(self, interaction: discord.Interaction):
        vc = interaction.guild.voice_client
        if not vc or not vc.is_paused():
            return await interaction.response.send_message("❌ Signal pipelines are not actively suspended.", ephemeral=True)
        
        state = self.get_state(interaction.guild.id)
        vc.resume()
        state.paused_duration += time.time() - state.pause_start_time
        await interaction.response.send_message("▶ Audio translation mapping resumed.")

    @app_commands.command(name="volume", description="Scale structural output parameters safely.")
    @app_commands.describe(percentage="Value scaling boundary integers ranging 1 to 100")
    async def volume(self, interaction: discord.Interaction, percentage: int):
        if not 1 <= percentage <= 100:
            return await interaction.response.send_message("❌ Out of bound parameters. Bound limits match 1-100 scales.", ephemeral=True)
        
        vc = interaction.guild.voice_client
        state = self.get_state(interaction.guild.id)
        state.volume = percentage / 100.0
        
        if vc and vc.source:
            if isinstance(vc.source, discord.PCMVolumeTransformer):
                vc.source.volume = state.volume
        
        await interaction.response.send_message(f"🔊 Audio scale transformations balanced: `{percentage}%`")

    @app_commands.command(name="queue", description="Display full active arrays tracking incoming songs.")
    async def queue(self, interaction: discord.Interaction):
        state = self.get_state(interaction.guild.id)
        if not state.queue and not state.current:
            return await interaction.response.send_message("ℹ Layout pipelines are completely empty right now.", ephemeral=True)

        lines = []
        if state.current:
            lines.append(f"**NOW PLAYING:**\n {state.current['title']} | `[{self.format_time(state.current['duration'])}]` \n")
        
        if state.queue:
            lines.append("**UPCOMING RELEASES:**")
            for i, track in enumerate(list(state.queue)[:15]):
                lines.append(f"`{i+1:02d}.` **{track['title']}** | `[{self.format_time(track['duration'])}]`")
            
            if len(state.queue) > 15:
                lines.append(f"\n*...and {len(state.queue) - 15} more alternative options stored inside memory tracking pipelines.*")
        
        embed = discord.Embed(title="CLOUT BUFFER STORAGE PROFILE LOGS", description="\n".join(lines), color=0x010101)
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="nowplaying", description="Isolate display data matching active track instances.")
    async def nowplaying(self, interaction: discord.Interaction):
        state = self.get_state(interaction.guild.id)
        if not state.current:
            return await interaction.response.send_message("❌ Systems reflect a pure idle operational processing mode.", ephemeral=True)

        embed = discord.Embed(title="ISOLATED TRACK RECOGNITION BLOCK METADATA", color=0x010101)
        embed.set_thumbnail(url=state.current.get("thumbnail"))
        embed.add_field(name="Identity Mapping Name String", value=f"yaml\n{state.current['title']}\n", inline=False)
        embed.add_field(name="Web Tracking Link URL", value=f"[Open Target Profile Page]({state.current['webpage_url']})", inline=True)
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="clearqueue", description="Flush structural buffer tracking tables instantly.")
    async def clearqueue(self, interaction: discord.Interaction):
        state = self.get_state(interaction.guild.id)
        state.queue.clear()
        await interaction.response.send_message("🧹 Queue table flushing algorithms executed. Buffer storage cleared.")

    @app_commands.command(name="history", description="Review historical track sequences executed across this session.")
    async def history(self, interaction: discord.Interaction):
        state = self.get_state(interaction.guild.id)
        if not state.history:
            return await interaction.response.send_message("ℹ Historical data tracker contains no valid entries.", ephemeral=True)

        lines = [f"`{i+1:02d}.` **{track['title']}** by {track['uploader']}" for i, track in enumerate(state.history)]
        embed = discord.Embed(title="SESSION HISTORICAL AUDIT TRAILS", description="\n".join(lines[-15:]), color=0x010101)
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="leave", description="Sever structural linkages to current voice connections.")
    async def leave(self, interaction: discord.Interaction):
        vc = interaction.guild.voice_client
        if not vc:
            return await interaction.response.send_message("❌ Current runtime state does not track voice interactions.", ephemeral=True)

        state = self.get_state(interaction.guild.id)
        state.clear()
        if state.controller_msg:
            try: await state.controller_msg.delete()
            except Exception: pass
            state.controller_msg = None

        await vc.disconnect()
        await interaction.response.send_message("👋 Voice matrix detached safely. Hardware allocations freed up.")

async def setup(bot: commands.Bot):
    """Cog distribution integration hook."""
    await bot.add_cog(Music(bot))
