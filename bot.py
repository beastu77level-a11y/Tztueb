import os
import sqlite3
import re
import asyncio
import time
import logging
import csv
import zipfile
import shutil
import html
import json
import traceback
from datetime import datetime

from telethon import TelegramClient, events, Button
from telethon.errors import (
    SessionPasswordNeededError,
    MessageNotModifiedError,
    UserNotParticipantError,
    ChatAdminRequiredError
)
from telethon.tl.types import (
    ReplyKeyboardMarkup,
    KeyboardButtonRow,
    KeyboardButton,
    KeyboardButtonWebView,
    MessageEntityCustomEmoji
)
from telethon.tl.functions.channels import GetParticipantRequest
from telethon.tl.functions.account import GetPasswordRequest
from telethon.tl.functions.messages import ExportChatInviteRequest

try:
    from dotenv import load_dotenv
    load_dotenv()
except Exception:
    pass


# ================= CONFIGURATION =================
API_ID = int(os.getenv("API_ID"))
API_HASH = os.getenv("API_HASH")
BOT_TOKEN = os.getenv("BOT_TOKEN")
ADMIN_ID = int(os.getenv("ADMIN_ID", "0"))  # 👑 MAIN ADMIN ID (set your numeric Telegram user ID)

# DEFAULT CHANNELS & DEPOSIT GROUP (Can be updated dynamically from Admin Panel -> Change Variables)
LOG_CHANNEL_ID = int(os.getenv("LOG_CHANNEL_ID", "0"))
VOUCH_CHANNEL_ID = int(os.getenv("VOUCH_CHANNEL_ID", "0"))
DEPOSIT_GROUP_ID = int(os.getenv("DEPOSIT_GROUP_ID", "0"))
DEPOSIT_GROUP_URL = os.getenv("DEPOSIT_GROUP_URL", "")
DEFAULT_TIP_BOT = os.getenv("DEFAULT_TIP_BOT", "cctip_bot")
DEFAULT_TIP_RECEIVER = os.getenv("DEFAULT_TIP_RECEIVER", "")

CHECK_CHANNELS = ["-1003972376338", "-1002421476696"]
JOIN_URLS = [
    "https://t.me/Freshtgsales",
    "https://t.me/+arhB_Cn_0o83ZDU1"
]

# LINKS
TERMS_URL = os.getenv("TERMS_URL", "https://tgtele.onrender.com/")

OTP_REGEX = r"\b\d{4,8}\b"
AUTO_CANCEL_SECONDS = 600
MIN_DEPOSIT_USDT = float(os.getenv("MIN_DEPOSIT_USDT", "0.5"))
DEFAULT_POINTS_PER_USD = float(os.getenv("DEFAULT_POINTS_PER_USD", "95.0"))  # 1$ = 95 Points


# ================= UNIVERSAL EVERYWHERE PREMIUM EMOJI INJECTOR =================
EMOJI_CHAR_TO_ID: dict[str, str] = {}

def _strip_vs(s: str) -> str:
    return s.replace("\ufe0f", "").replace("\ufe0e", "")

def rebuild_emoji_char_map():
    """Rebuilds EMOJI_CHAR_TO_ID from PREMIUM_EMOJI_MAP, DEFAULT_EMOJIS, and custom char mappings."""
    EMOJI_CHAR_TO_ID.clear()
    for key, eid in PREMIUM_EMOJI_MAP.items():
        if eid and str(eid).strip().isdigit():
            fb = DEFAULT_EMOJIS.get(key)
            if fb:
                EMOJI_CHAR_TO_ID[_strip_vs(fb)] = str(eid).strip()
    try:
        raw_char_map = get_ui_setting("custom_emoji_char_map")
        if raw_char_map:
            extra = json.loads(raw_char_map)
            if isinstance(extra, dict):
                for ch_em, eid in extra.items():
                    if ch_em and eid and str(eid).strip().isdigit():
                        EMOJI_CHAR_TO_ID[_strip_vs(str(ch_em))] = str(eid).strip()
    except Exception:
        pass

def apply_global_premium_emojis(text: str | None) -> str | None:
    """Replaces configured normal emojis in HTML text with <tg-emoji emoji-id="...">...</tg-emoji>
    everywhere in bot messages, while avoiding <tg-emoji> tags and <code>/<pre> blocks."""
    if not text or not isinstance(text, str) or not EMOJI_CHAR_TO_ID:
        return text
    tokens = re.split(
        r'(<tg-emoji\b[^>]*>.*?</tg-emoji>|<code\b[^>]*>.*?</code>|<pre\b[^>]*>.*?</pre>|<[^>]+>)',
        text,
        flags=re.DOTALL | re.IGNORECASE
    )
    out = []
    sorted_emojis = sorted(EMOJI_CHAR_TO_ID.items(), key=lambda kv: len(kv[0]), reverse=True)
    for tok in tokens:
        if not tok:
            continue
        if tok.startswith("<"):
            out.append(tok)
            continue
        new_tok = tok
        for norm_em, eid in sorted_emojis:
            chars = "".join(
                ch + "(?:\ufe0f|\ufe0e)?" if ch not in ("\ufe0f", "\ufe0e") else ""
                for ch in norm_em
            )
            if not chars:
                continue
            pattern = re.compile(chars)
            new_tok = pattern.sub(lambda m, _eid=eid: f'<tg-emoji emoji-id="{_eid}">{m.group(0)}</tg-emoji>', new_tok)
        out.append(new_tok)
    return "".join(out)


def _is_non_deposit_group_entity(entity) -> bool:
    """Returns True if `entity` resolves to a group/supergroup that is NOT the configured Deposit Group."""
    try:
        dep_grp_id = get_deposit_group_id()
        # Extract target numeric chat/channel id if possible
        target_id = None
        if isinstance(entity, int):
            target_id = entity
        elif isinstance(entity, str) and entity.lstrip("-").isdigit():
            target_id = int(entity)
        elif hasattr(entity, "id"):
            eid = int(entity.id)
            if getattr(entity, "megagroup", False) or getattr(entity, "broadcast", False) or str(type(entity).__name__).lower().find("channel") != -1:
                target_id = int(f"-100{eid}") if not str(eid).startswith("-100") else eid
            else:
                target_id = -abs(eid)

        if target_id is not None:
            # If it's a negative ID (group/supergroup/channel)
            if target_id < 0:
                # Allow if it matches configured deposit group ID
                if dep_grp_id and int(target_id) == int(dep_grp_id):
                    return False
                # Also check if dep_grp_id was stored without -100 prefix
                if dep_grp_id and str(abs(int(target_id))).endswith(str(abs(int(dep_grp_id)))):
                    return False
                # If it's a channel/supergroup/group other than deposit group, block sending messages there
                return True
    except Exception:
        pass
    return False

def _patch_telethon_outbound_html():
    """Hooks Telethon client outbound message/edit/file methods so configured emojis render everywhere
    and blocks outbound messages/files to any group other than the Deposit Group."""
    orig_send_message = bot.send_message
    orig_send_file = bot.send_file
    orig_edit_message = bot.edit_message

    async def _wrapped_send_message(entity, message='', *args, **kwargs):
        if _is_non_deposit_group_entity(entity):
            return None
        if isinstance(message, str) and kwargs.get('parse_mode', bot.parse_mode) == 'html':
            message = apply_global_premium_emojis(message)
        return await orig_send_message(entity, message, *args, **kwargs)

    async def _wrapped_send_file(entity, file, *args, **kwargs):
        if _is_non_deposit_group_entity(entity):
            return None
        caption = kwargs.get('caption')
        if isinstance(caption, str) and kwargs.get('parse_mode', bot.parse_mode) == 'html':
            kwargs['caption'] = apply_global_premium_emojis(caption)
        return await orig_send_file(entity, file, *args, **kwargs)

    async def _wrapped_edit_message(entity, message, text=None, *args, **kwargs):
        if isinstance(text, str) and kwargs.get('parse_mode', bot.parse_mode) == 'html':
            text = apply_global_premium_emojis(text)
        elif isinstance(message, str) and text is None and kwargs.get('parse_mode', bot.parse_mode) == 'html':
            message = apply_global_premium_emojis(message)
        return await orig_edit_message(entity, message, text, *args, **kwargs)

    bot.send_message = _wrapped_send_message
    bot.send_file = _wrapped_send_file
    bot.edit_message = _wrapped_edit_message


# ================= 10-LANGUAGE ENGINE =================
SUPPORTED_LANGUAGES = [
    ("en", "🇺🇸 English"),
    ("ru", "🇷🇺 Русский"),
    ("fa", "🇮🇷 فارسی"),
    ("zh", "🇨🇳 中文"),
    ("es", "🇪🇸 Español"),
    ("fr", "🇫🇷 Français"),
    ("ar", "🇸🇦 العربية"),
    ("pt", "🇵🇹 Português"),
    ("id", "🇮🇩 Bahasa Indonesia"),
    ("hi", "🇮🇳 हिन्दी"),
]

LANG_CODES = {code for code, _ in SUPPORTED_LANGUAGES}

TRANSLATIONS = {
    "en": {
        "choose_lang_title": "🌐 <b>Choose Your Language</b>",
        "choose_lang_desc": "Select the language you want to use in the bot.",
        "lang_updated": "✅ Language updated to <b>English</b>!",
        "lang_set_continue": "✅ Language set to <b>English</b>!",
        "btn_language": "Language",
        "btn_buy_account": "Buy Account",
        "btn_my_profile": "My Profile",
        "btn_buy_sessions": "Buy Sessions",
        "btn_deposit": "Deposit",
        "btn_my_stats": "My Stats",
        "btn_support": "Support",
        "btn_admin_panel": "Admin Panel",
        "btn_choose_lang": "🌐 Language",
        "btn_join_ch": "📢 Join {title}",
        "btn_verify_join": "✅ Verify Joined",
        "btn_read_terms": "📜 Read Terms & Conditions",
        "btn_accept": "✅ Accept",
        "btn_reject": "❌ Reject",
        "btn_cancel": "❌ Cancel",
        "btn_back": "🔙 Back",
        "btn_prev": "⬅️ Prev",
        "btn_next": "➡️ Next",
        "btn_buy_now": "✅ Yes, Buy Now",
        "btn_get_otp_again": "🔄 Get OTP Again",
        "btn_logout": "🚪 Finish & Logout",
        "btn_purchase_logs": "📜 View Purchase Logs",
        "btn_referral_logs": "👥 Referral Logs",
        "btn_join_dep_grp": "🏦 Join Deposit Group",
        "btn_contact_support": "📩 Contact Support",
        "bot_maintenance": "{off} <b>Bot is currently under maintenance.</b> Please try again later.",
        "bot_maintenance_alert": "⚙️ Bot is under maintenance.",
        "slow_down": "⚠️ Please slow down! Don't spam buttons.",
        "banned_alert": "🚫 BANNED",
        "force_join_msg": "{warn} <b>You must join our channels first!</b>",
        "must_join_alert": "⚠️ You must join the channels first!",
        "terms_msg": "{doc} <b>TERMS & CONDITIONS</b>\nPlease read and accept our Terms & Conditions before using the bot.",
        "terms_accepted_alert": "✅ Terms Accepted!",
        "terms_rejected_msg": "{no} You cannot use the bot without accepting the terms.",
        "cancelled_msg": "{no} <b>Cancelled.</b>",
        "welcome_msg": "👋 <b>Welcome to Fresh Tg Store!</b>\n\n{pts} <b>Currency Rate:</b> <code>$1 USDT = {rate} Points</code>\n{gift} <b>Refer & Earn:</b>\nInvite friends and earn {pct}% of their deposits in Points!\n{globe} <code>https://t.me/{bot_user}?start=ref_{ref_uid}</code>",
        "init_error": "⚠️ Error: Please type /start to initialize your account.",
        "profile_msg": "{acc} <b>USER PROFILE</b>\n\n{id_e} User ID: <code>{uid}</code>\n{pts} Balance: <code>{bal} Pts (${usd_bal:.2f})</code>\n{card} Deposited: <code>{dep} Pts (${usd_dep:.2f})</code>{disc_msg}\n{cal} Joined: {joined}\n\n{users} <b>Your Referral Link:</b>\n<code>{ref_link}</code>\n\n<i>(Share this link with your friends to earn Points bonuses!)</i>",
        "active_discount": "\n{gift} Active Discount: <b>{discount}% OFF</b>",
        "stats_msg": "{stats} <b>My Statistics</b>\n\n{cart} <b>Accounts Bought:</b> {orders}\n{pts} <b>Total Spent:</b> {spent} Pts (${usd_spent:.2f})\n{card} <b>Total Deposited:</b> {dep} Pts (${usd_dep:.2f})",
        "ref_count_alert": "👥 You have referred {count} user(s).",
        "purchase_hist_title": "{doc} <b>Purchase History (Page {page})</b>\n\n",
        "no_purchases": "No purchases found.",
        "stock_empty": "{no} <b>Stock is Empty right now. Check back later!</b>",
        "bulk_menu": "{store} <b>Bulk Sessions Menu</b>",
        "single_menu": "{cart} <b>Single Account Menu</b>",
        "select_region": "{title}\n\n{globe} <b>Select a Region below to view available numbers (Page {page}).</b>\n{usdt} Rate: $1 USDT = <b>{rate} Points</b>\n\n",
        "out_of_stock_alert": "❌ Out of stock for this country.",
        "out_of_stock_short": "❌ Out of stock!",
        "select_year_msg": "{cal} <b>Select Account Year</b>\n{globe} Country: <b>{country}</b>\n\n",
        "confirm_buy_msg": "{cart} <b>Confirm Your Purchase</b>\n\n{flag} <b>Country:</b> {country}\n{cal} <b>Year:</b> {year}\n{pts} <b>Final Price:</b> <b>{price} Pts</b> (${usd_price:.2f})\n\n{card} <b>Your Balance:</b> <b>{bal} Pts</b>\n\n❓ Do you want to proceed with this purchase?",
        "sold_out_alert": "❌ Sold out! Another user just bought this account.",
        "insufficient_bal_alert": "❌ Insufficient Balance! Need {price} Pts",
        "insufficient_bal_msg": "{no} <b>Insufficient Balance!</b>\nYou need <b>{cost} Pts</b> to buy {qty} sessions.",
        "fetching_num": "🔄 <b>Fetching Number (+{phone})...</b>",
        "acc_invalid": "{no} <b>Account Invalid.</b> Points refunded. Try buying another.",
        "order_active_msg": "{yes} <b>Order Active!</b>\n\n{phone_e} <b>Phone:</b> <code>{phone}</code>\n{flag} <b>Country:</b> {c_icon} {country}\n\n🔻 <b>INSTRUCTIONS:</b>\n1. Open Telegram & Add Account\n2. Enter the number above.\n3. {wait} <b>Please wait!</b> The bot is actively listening for your OTP and will send it automatically once Telegram delivers it.\n\n<i>Note: If no OTP is received within 10 minutes, the bot will auto-cancel and refund your Points automatically.</i>",
        "otp_fetched_msg": "{yes} <b>Latest OTP Fetched!</b>\n\n{phone_e} <b>Phone:</b> <code>{phone}</code>\n{flag} <b>Country:</b> {c_icon} {country}\n{otp_e} <b>OTP:</b> <code>{code}</code>\n{twofa_line}",
        "twofa_enabled": "{twofa} <b>2FA:</b> <code>{pwd}</code>",
        "twofa_disabled": "🔓 <b>2FA:</b> <code>Disabled (No Password)</code>",
        "order_expired_msg": "{time_e} <b>Order Expired!</b>\nThe 10-minute limit for <code>{phone}</code> ran out. Your Points (<b>{price} Pts</b>) have been automatically refunded.",
        "session_logged_out_alert": "⚠️ Session already logged out or expired.",
        "fetching_otp_toast": "🔄 Fetching latest OTP...",
        "no_new_otp_alert": "⏳ No new OTP found yet. Try again in a few seconds.",
        "otp_err_alert": "❌ Error fetching OTP.",
        "session_finished_msg": "{yes} <b>Session Finished & Logged out successfully.</b>",
        "no_active_order_alert": "⚠️ No active order found or already logged out.",
        "bulk_prompt_msg": "{store} <b>Buy {country} ({year}) Sessions</b>\n\n{pts} <b>Price per session:</b> <b>{price} Pts</b>\n{pkg} <b>Available Stock:</b> {stock}\n\n👇 <b>Reply to this message</b> with the <b>Number of Sessions</b> you want to buy.",
        "not_enough_stock_msg": "{warn} <b>Not enough stock!</b> Max is {stock}.",
        "enter_valid_num_msg": "{no} Please enter a valid number.",
        "processing_sessions_msg": "{wait} <b>Processing your sessions...</b>",
        "stock_changed_msg": "{no} Stock changed during processing. Purchase Cancelled.",
        "bulk_success_caption": "{yes} <b>Bulk Purchase Successful!</b>\n\n{flag} Country: {country}\n{pkg} Quantity: {qty}\n{pts} Total Paid: <b>{cost} Pts</b>\n\n<i>(Note: Sessions are safely provided, the bot does not keep them active)</i>",
        "zip_err_msg": "{warn} Error creating zip: {err}",
        "support_msg": "{on} <b>Fresh Tg Support & Relevant Information</b>\n\n{warn} For Support Contact Admin ..",
        "btn_support_url": "📩 Support",
        "btn_terms_url": "📜 Terms & Conditions",
        "btn_channel_url": "📢 Channel",
        "dep_group_unavail": "{warn} <b>Deposit Group Unavailable</b>\nPlease contact Support for assistance.",
        "dep_menu_msg": "{money} <b>PREMIUM USDT DEPOSIT PORTAL</b>\n━━━━━━━━━━━━━━━━━━━━━━\n{pts} <b>Exchange Rate:</b> <code>$1 USDT = {rate} Points</code>\n{asst} <b>Tip Processor:</b> <code>@{tip_bot}</code>\n{acc} <b>Tip Recipient:</b> <code>@{receiver}</code>\n\n<b>How to Deposit:</b>\n1. Join the official Deposit Group using the button below.\n2. Send your tip (directly or by replying to the recipient):\n   <code>cc (amount) usdt @{receiver}</code>\n3. Once <code>@{tip_bot}</code> confirms your tip, Points are credited automatically and you are removed from the group in 5 seconds.\n\n{warn} <b>Important Notice:</b>\n• Deposits below <b>0.5 USDT</b> will <b>not</b> be counted. If you sent less than 0.5 USDT, please contact Support.\n• Idle members who do not send a message within <b>2 minutes</b> of joining are automatically removed.",
        "grp_welcome_msg": "{spark} <b>DEPOSIT INSTRUCTIONS</b> — {mention}\n━━━━━━━━━━━━━━━━━━━━━━\n{money} Send your tip (directly or by replying to the recipient):\n<code>cc (deposit amount) usdt @{receiver}</code>\n<i>Example:</i> <code>cc 5 usdt @{receiver}</code>\n\n{pts} <b>Rate:</b> <code>$1 USDT = {rate} Points</code>\n\n{warn} <b>Important Rules:</b>\n• Deposits under <b>0.5 USDT</b> will <b>not</b> be counted. If you sent less than 0.5 USDT, please contact Support.\n• Please send a message within <b>2 minutes</b> of joining, or you will be removed automatically.",
        "grp_inactive_kick": "{time_e} <a href='tg://user?id={uid}'>Member</a> was removed after 2 minutes of inactivity.",
        "grp_wrong_token": "{warn} <a href='tg://user?id={uid}'>Member</a>, unsupported token detected in your tip.\nOnly <b>USDT</b> deposits are supported automatically—please contact <b>Support</b> for assistance.",
        "grp_wrong_token_anon": "{warn} Unsupported token tip detected. Only <b>USDT</b> deposits are supported—please contact <b>Support</b> for assistance.",
        "grp_min_warn": "{warn} <a href='tg://user?id={uid}'>Member</a>, your deposit of <b>{amt} USDT</b> is below the <b>0.5 USDT</b> minimum.\nDeposits under <b>0.5 USDT</b> are not counted—please contact <b>Support</b> if you have already sent funds.",
        "grp_confirmed": "{yes} <a href='tg://user?id={uid}'>Deposit Confirmed</a> — <b>+{pts} Points</b> (${amt:.2f} USDT) credited.\n<i>Removing you from the deposit group in 5 seconds...</i>",
        "dm_deposit_credited": "{yes} Deposit Credited — <b>{pts} Points</b> (${amt:.2f} USDT) added to your account.\n{pts} Updated Balance: <b>{bal} Points</b> | Rate: $1 = {rate} Points.",
    },
    "hi": {
        "choose_lang_title": "🌐 <b>अपनी भाषा चुनें</b>",
        "choose_lang_desc": "बॉट में उपयोग करने के लिए अपनी भाषा चुनें।",
        "lang_updated": "✅ भाषा <b>हिन्दी</b> में बदल दी गई है!",
        "lang_set_continue": "✅ भाषा <b>हिन्दी</b> सेट हो गई है!",
        "btn_language": "भाषा",
        "btn_buy_account": "अकाउंट खरीदें",
        "btn_my_profile": "मेरी प्रोफ़ाइल",
        "btn_buy_sessions": "सेशन्स खरीदें",
        "btn_deposit": "डिपॉज़िट",
        "btn_my_stats": "मेरे आंकड़े",
        "btn_support": "सपोर्ट",
        "btn_admin_panel": "एडमिन पैनल",
        "btn_choose_lang": "🌐 भाषा / Language",
        "btn_join_ch": "📢 चैनल जॉइन करें ({title})",
        "btn_verify_join": "✅ जॉइन वेरिफाई करें",
        "btn_read_terms": "📜 नियम और शर्तें पढ़ें",
        "btn_accept": "✅ स्वीकार करें",
        "btn_reject": "❌ अस्वीकार करें",
        "btn_cancel": "❌ रद्द करें",
        "btn_back": "🔙 वापस",
        "btn_prev": "⬅️ पिछला",
        "btn_next": "➡️ अगला",
        "btn_buy_now": "✅ हाँ, अभी खरीदें",
        "btn_get_otp_again": "🔄 फिर से OTP लें",
        "btn_logout": "🚪 समाप्त करें और लॉगआउट करें",
        "btn_purchase_logs": "📜 खरीद इतिहास देखें",
        "btn_referral_logs": "👥 रेफ़रल रिकॉर्ड",
        "btn_join_dep_grp": "🏦 डिपॉज़िट ग्रुप जॉइन करें",
        "btn_contact_support": "📩 सपोर्ट से संपर्क करें",
        "bot_maintenance": "{off} <b>बॉट अभी रखरखाव (Maintenance) में है।</b> कृपया बाद में प्रयास करें।",
        "bot_maintenance_alert": "⚙️ बॉट रखरखाव में है।",
        "slow_down": "⚠️ कृपया थोड़ा रुकें! बटन बार-बार न दबाएं।",
        "banned_alert": "🚫 प्रतिबंधित (BANNED)",
        "force_join_msg": "{warn} <b>बॉट उपयोग करने से पहले हमारे चैनल जॉइन करें!</b>",
        "must_join_alert": "⚠️ पहले चैनल जॉइन करना ज़रूरी है!",
        "terms_msg": "{doc} <b>नियम और शर्तें</b>\nकृपया बॉट उपयोग करने से पहले नियम और शर्तें पढ़ें और स्वीकार करें।",
        "terms_accepted_alert": "✅ नियम स्वीकार किए गए!",
        "terms_rejected_msg": "{no} नियम स्वीकार किए बिना आप बॉट का उपयोग नहीं कर सकते।",
        "cancelled_msg": "{no} <b>रद्द कर दिया गया।</b>",
        "welcome_msg": "👋 <b>Fresh Tg Store में आपका स्वागत है!</b>\n\n{pts} <b>पॉइंट्स दर:</b> <code>$1 USDT = {rate} Points</code>\n{gift} <b>रेफ़र करें और कमाएं:</b>\nदोस्तों को आमंत्रित करें और उनके डिपॉज़िट का {pct}% पॉइंट्स में पाएं!\n{globe} <code>https://t.me/{bot_user}?start=ref_{ref_uid}</code>",
        "init_error": "⚠️ त्रुटि: कृपया अपना अकाउंट शुरू करने के लिए /start टाइप करें।",
        "profile_msg": "{acc} <b>उपयोगकर्ता प्रोफ़ाइल</b>\n\n{id_e} यूज़र ID: <code>{uid}</code>\n{pts} बैलेंस: <code>{bal} Pts (${usd_bal:.2f})</code>\n{card} कुल डिपॉज़िट: <code>{dep} Pts (${usd_dep:.2f})</code>{disc_msg}\n{cal} जॉइन तिथि: {joined}\n\n{users} <b>आपका रेफ़रल लिंक:</b>\n<code>{ref_link}</code>\n\n<i>(पॉइंट्स बोनस कमाने के लिए यह लिंक दोस्तों के साथ साझा करें!)</i>",
        "active_discount": "\n{gift} सक्रिय छूट: <b>{discount}% OFF</b>",
        "stats_msg": "{stats} <b>मेरे आंकड़े</b>\n\n{cart} <b>खरीदे गए अकाउंट्स:</b> {orders}\n{pts} <b>कुल खर्च:</b> {spent} Pts (${usd_spent:.2f})\n{card} <b>कुल डिपॉज़िट:</b> {dep} Pts (${usd_dep:.2f})",
        "ref_count_alert": "👥 आपने {count} उपयोगकर्ता को रेफ़र किया है।",
        "purchase_hist_title": "{doc} <b>खरीद इतिहास (पेज {page})</b>\n\n",
        "no_purchases": "कोई खरीद नहीं मिली।",
        "stock_empty": "{no} <b>अभी स्टॉक खाली है। बाद में जांचें!</b>",
        "bulk_menu": "{store} <b>बल्क सेशन्स मेनू</b>",
        "single_menu": "{cart} <b>सिंगल अकाउंट मेनू</b>",
        "select_region": "{title}\n\n{globe} <b>उपलब्ध नंबर देखने के लिए देश चुनें (पेज {page})।</b>\n{usdt} दर: $1 USDT = <b>{rate} Points</b>\n\n",
        "out_of_stock_alert": "❌ इस देश के लिए स्टॉक उपलब्ध नहीं है।",
        "out_of_stock_short": "❌ स्टॉक समाप्त!",
        "select_year_msg": "{cal} <b>अकाउंट वर्ष चुनें</b>\n{globe} देश: <b>{country}</b>\n\n",
        "confirm_buy_msg": "{cart} <b>खरीद की पुष्टि करें</b>\n\n{flag} <b>देश:</b> {country}\n{cal} <b>वर्ष:</b> {year}\n{pts} <b>अंतिम मूल्य:</b> <b>{price} Pts</b> (${usd_price:.2f})\n\n{card} <b>आपका बैलेंस:</b> <b>{bal} Pts</b>\n\n❓ क्या आप यह खरीद जारी रखना चाहते हैं?",
        "sold_out_alert": "❌ समाप्त हो गया! किसी अन्य यूज़र ने यह अकाउंट खरीद लिया है।",
        "insufficient_bal_alert": "❌ अपर्याप्त बैलेंस! {price} Pts आवश्यक हैं",
        "insufficient_bal_msg": "{no} <b>अपर्याप्त बैलेंस!</b>\n{qty} सेशन्स खरीदने के लिए आपको <b>{cost} Pts</b> चाहिए।",
        "fetching_num": "🔄 <b>नंबर प्राप्त किया जा रहा है (+{phone})...</b>",
        "acc_invalid": "{no} <b>अकाउंट अमान्य है।</b> पॉइंट्स वापस कर दिए गए हैं। दूसरा अकाउंट आज़माएं।",
        "order_active_msg": "{yes} <b>ऑर्डर सक्रिय है!</b>\n\n{phone_e} <b>फ़ोन:</b> <code>{phone}</code>\n{flag} <b>देश:</b> {c_icon} {country}\n\n🔻 <b>निर्देश:</b>\n1. Telegram खोलें और Add Account चुनें\n2. ऊपर दिया गया नंबर दर्ज करें।\n3. {wait} <b>कृपया प्रतीक्षा करें!</b> बॉट आपके OTP का इंतज़ार कर रहा है और आते ही भेज देगा।\n\n<i>नोट: 10 मिनट में OTP न मिलने पर बॉट स्वतः ऑर्डर रद्द करके पॉइंट्स वापस कर देगा।</i>",
        "otp_fetched_msg": "{yes} <b>नवीनतम OTP प्राप्त हुआ!</b>\n\n{phone_e} <b>फ़ोन:</b> <code>{phone}</code>\n{flag} <b>देश:</b> {c_icon} {country}\n{otp_e} <b>OTP:</b> <code>{code}</code>\n{twofa_line}",
        "twofa_enabled": "{twofa} <b>2FA:</b> <code>{pwd}</code>",
        "twofa_disabled": "🔓 <b>2FA:</b> <code>बंद (कोई पासवर्ड नहीं)</code>",
        "order_expired_msg": "{time_e} <b>ऑर्डर समाप्त हो गया!</b>\n<code>{phone}</code> के लिए 10 मिनट की समय सीमा समाप्त हो गई। आपके <b>{price} Pts</b> स्वतः वापस कर दिए गए हैं।",
        "session_logged_out_alert": "⚠️ सेशन पहले ही लॉगआउट या समाप्त हो चुका है।",
        "fetching_otp_toast": "🔄 नवीनतम OTP लाया जा रहा है...",
        "no_new_otp_alert": "⏳ अभी नया OTP नहीं मिला है। कुछ सेकंड बाद पुनः प्रयास करें।",
        "otp_err_alert": "❌ OTP लाने में त्रुटि हुई।",
        "session_finished_msg": "{yes} <b>सेशन समाप्त और सफलतापूर्वक लॉगआउट हो गया।</b>",
        "no_active_order_alert": "⚠️ कोई सक्रिय ऑर्डर नहीं मिला या पहले ही लॉगआउट हो चुका है।",
        "bulk_prompt_msg": "{store} <b>{country} ({year}) सेशन्स खरीदें</b>\n\n{pts} <b>प्रति सेशन मूल्य:</b> <b>{price} Pts</b>\n{pkg} <b>उपलब्ध स्टॉक:</b> {stock}\n\n👇 खरीदने के लिए <b>सेशन्स की संख्या</b> लिखकर इस संदेश का उत्तर दें।",
        "not_enough_stock_msg": "{warn} <b>पर्याप्त स्टॉक नहीं है!</b> अधिकतम {stock} उपलब्ध हैं।",
        "enter_valid_num_msg": "{no} कृपया मान्य संख्या दर्ज करें।",
        "processing_sessions_msg": "{wait} <b>आपके सेशन्स प्रोसेस हो रहे हैं...</b>",
        "stock_changed_msg": "{no} प्रोसेसिंग के दौरान स्टॉक बदल गया। खरीद रद्द की गई।",
        "bulk_success_caption": "{yes} <b>बल्क खरीद सफल रही!</b>\n\n{flag} देश: {country}\n{pkg} मात्रा: {qty}\n{pts} कुल भुगतान: <b>{cost} Pts</b>\n\n<i>(नोट: सेशन्स सुरक्षित रूप से प्रदान किए गए हैं, बॉट उन्हें सक्रिय नहीं रखता)</i>",
        "zip_err_msg": "{warn} ZIP बनाने में त्रुटि: {err}",
        "support_msg": "{on} <b>Fresh Tg सपोर्ट और महत्वपूर्ण जानकारी</b>\n\n{warn} सहायता के लिए एडमिन से संपर्क करें..",
        "btn_support_url": "📩 सपोर्ट",
        "btn_terms_url": "📜 नियम और शर्तें",
        "btn_channel_url": "📢 चैनल",
        "dep_group_unavail": "{warn} <b>डिपॉज़िट ग्रुप उपलब्ध नहीं है</b>\nसहायता के लिए सपोर्ट से संपर्क करें।",
        "dep_menu_msg": "{money} <b>प्रीमियम USDT डिपॉज़िट पोर्टल</b>\n━━━━━━━━━━━━━━━━━━━━━━\n{pts} <b>विनिमय दर:</b> <code>$1 USDT = {rate} Points</code>\n{asst} <b>टिप प्रोसेसर:</b> <code>@{tip_bot}</code>\n{acc} <b>टिप प्राप्तकर्ता:</b> <code>@{receiver}</code>\n\n<b>डिपॉज़िट कैसे करें:</b>\n1. नीचे दिए बटन से आधिकारिक डिपॉज़िट ग्रुप जॉइन करें।\n2. ग्रुप में अपना टिप भेजें (सीधे या प्राप्तकर्ता को रिप्लाई करके):\n   <code>cc (amount) usdt @{receiver}</code>\n3. <code>@{tip_bot}</code> टिप कन्फ़र्म करते ही पॉइंट्स स्वतः जुड़ जाएंगे और 5 सेकंड में आपको ग्रुप से हटा दिया जाएगा।\n\n{warn} <b>महत्वपूर्ण सूचना:</b>\n• <b>0.5 USDT</b> से कम के डिपॉज़िट गिने <b>नहीं</b> जाएंगे। यदि आपने 0.5 USDT से कम भेजा है, तो सपोर्ट से संपर्क करें।\n• जॉइन करने के <b>2 मिनट</b> के भीतर संदेश न भेजने पर आपको स्वतः हटा दिया जाएगा।",
        "grp_welcome_msg": "{spark} <b>डिपॉज़िट निर्देश</b> — {mention}\n━━━━━━━━━━━━━━━━━━━━━━\n{money} अपना टिप भेजें (सीधे या प्राप्तकर्ता को रिप्लाई करके):\n<code>cc (deposit amount) usdt @{receiver}</code>\n<i>उदाहरण:</i> <code>cc 5 usdt @{receiver}</code>\n\n{pts} <b>दर:</b> <code>$1 USDT = {rate} Points</code>\n\n{warn} <b>महत्वपूर्ण नियम:</b>\n• <b>0.5 USDT</b> से कम के डिपॉज़िट गिने <b>नहीं</b> जाएंगे। यदि आपने 0.5 USDT से कम भेजा है, तो सपोर्ट से संपर्क करें।\n• कृपया जॉइन करने के <b>2 मिनट</b> के भीतर संदेश भेजें, अन्यथा आपको स्वतः हटा दिया जाएगा।",
        "grp_inactive_kick": "{time_e} <a href='tg://user?id={uid}'>सदस्य</a> को 2 मिनट की निष्क्रियता के बाद हटा दिया गया।",
        "grp_wrong_token": "{warn} <a href='tg://user?id={uid}'>सदस्य</a>, आपके टिप में असमर्थित टोकन मिला है।\nकेवल <b>USDT</b> डिपॉज़िट ही स्वतः मान्य हैं—सहायता के लिए कृपया <b>सपोर्ट</b> से संपर्क करें।",
        "grp_wrong_token_anon": "{warn} असमर्थित टोकन टिप मिला है। केवल <b>USDT</b> डिपॉज़िट ही स्वतः मान्य हैं—कृपया <b>सपोर्ट</b> से संपर्क करें।",
        "grp_min_warn": "{warn} <a href='tg://user?id={uid}'>सदस्य</a>, आपका <b>{amt} USDT</b> डिपॉज़िट न्यूनतम <b>0.5 USDT</b> से कम है।\n<b>0.5 USDT</b> से कम के डिपॉज़िट गिने नहीं जाते—यदि आप पहले ही भुगतान कर चुके हैं तो कृपया <b>सपोर्ट</b> से संपर्क करें।",
        "grp_confirmed": "{yes} <a href='tg://user?id={uid}'>डिपॉज़िट कन्फ़र्म हुआ</a> — <b>+{pts} Points</b> (${amt:.2f} USDT) जोड़े गए।\n<i>5 सेकंड में आपको डिपॉज़िट ग्रुप से हटाया जा रहा है...</i>",
        "dm_deposit_credited": "{yes} डिपॉज़िट कन्फ़र्म हुआ — आपके अकाउंट में <b>{pts} Points</b> (${amt:.2f} USDT) जोड़े गए।\n{pts} नया बैलेंस: <b>{bal} Points</b> | दर: $1 = {rate} Points।",
    },
    "ru": {
        "choose_lang_title": "🌐 <b>Выберите язык</b>",
        "choose_lang_desc": "Выберите язык, который хотите использовать в боте.",
        "lang_updated": "✅ Язык изменён на <b>Русский</b>!",
        "lang_set_continue": "✅ Выбран язык: <b>Русский</b>!",
        "btn_language": "Язык",
        "btn_buy_account": "Купить аккаунт",
        "btn_my_profile": "Мой профиль",
        "btn_buy_sessions": "Купить сессии",
        "btn_deposit": "Пополнить",
        "btn_my_stats": "Моя статистика",
        "btn_support": "Поддержка",
        "btn_admin_panel": "Админ-панель",
        "btn_choose_lang": "🌐 Язык / Language",
        "btn_join_ch": "📢 Вступить в канал ({title})",
        "btn_verify_join": "✅ Проверить подписку",
        "btn_read_terms": "📜 Правила и условия",
        "btn_accept": "✅ Принять",
        "btn_reject": "❌ Отклонить",
        "btn_cancel": "❌ Отмена",
        "btn_back": "🔙 Назад",
        "btn_prev": "⬅️ Назад",
        "btn_next": "➡️ Далее",
        "btn_buy_now": "✅ Да, купить сейчас",
        "btn_get_otp_again": "🔄 Получить код снова",
        "btn_logout": "🚪 Завершить и выйти",
        "btn_purchase_logs": "📜 История покупок",
        "btn_referral_logs": "👥 Рефералы",
        "btn_join_dep_grp": "🏦 Группа пополнения",
        "btn_contact_support": "📩 Поддержка",
        "bot_maintenance": "{off} <b>Бот на техническом обслуживании.</b> Попробуйте позже.",
        "bot_maintenance_alert": "⚙️ Бот на обслуживании.",
        "slow_down": "⚠️ Не нажимайте кнопки слишком быстро!",
        "banned_alert": "🚫 ЗАБЛОКИРОВАНО",
        "force_join_msg": "{warn} <b>Сначала подпишитесь на наши каналы!</b>",
        "must_join_alert": "⚠️ Сначала необходимо подписаться на каналы!",
        "terms_msg": "{doc} <b>ПРАВИЛА И УСЛОВИЯ</b>\nПожалуйста, прочтите и примите правила перед использованием бота.",
        "terms_accepted_alert": "✅ Правила приняты!",
        "terms_rejected_msg": "{no} Вы не можете использовать бота без принятия правил.",
        "cancelled_msg": "{no} <b>Отменено.</b>",
        "welcome_msg": "👋 <b>Добро пожаловать в Fresh Tg Store!</b>\n\n{pts} <b>Курс:</b> <code>$1 USDT = {rate} Points</code>\n{gift} <b>Реферальная программа:</b>\nПриглашайте друзей и получайте {pct}% от их пополнений в поинтах!\n{globe} <code>https://t.me/{bot_user}?start=ref_{ref_uid}</code>",
        "init_error": "⚠️ Ошибка: введите /start для инициализации аккаунта.",
        "profile_msg": "{acc} <b>ПРОФИЛЬ ПОЛЬЗОВАТЕЛЯ</b>\n\n{id_e} ID пользователя: <code>{uid}</code>\n{pts} Баланс: <code>{bal} Pts (${usd_bal:.2f})</code>\n{card} Пополнено: <code>{dep} Pts (${usd_dep:.2f})</code>{disc_msg}\n{cal} Регистрация: {joined}\n\n{users} <b>Ваша реферальная ссылка:</b>\n<code>{ref_link}</code>\n\n<i>(Делитесь ссылкой с друзьями и получайте бонусы в поинтах!)</i>",
        "active_discount": "\n{gift} Активная скидка: <b>{discount}% OFF</b>",
        "stats_msg": "{stats} <b>Моя статистика</b>\n\n{cart} <b>Куплено аккаунтов:</b> {orders}\n{pts} <b>Всего потрачено:</b> {spent} Pts (${usd_spent:.2f})\n{card} <b>Всего пополнено:</b> {dep} Pts (${usd_dep:.2f})",
        "ref_count_alert": "👥 Вы пригласили пользователей: {count}.",
        "purchase_hist_title": "{doc} <b>История покупок (Стр. {page})</b>\n\n",
        "no_purchases": "Покупок не найдено.",
        "stock_empty": "{no} <b>Наличие временно отсутствует. Зайдите позже!</b>",
        "bulk_menu": "{store} <b>Массовая покупка сессий</b>",
        "single_menu": "{cart} <b>Покупка одного аккаунта</b>",
        "select_region": "{title}\n\n{globe} <b>Выберите регион для просмотра доступных номеров (Стр. {page}).</b>\n{usdt} Курс: $1 USDT = <b>{rate} Points</b>\n\n",
        "out_of_stock_alert": "❌ Нет в наличии для этой страны.",
        "out_of_stock_short": "❌ Нет в наличии!",
        "select_year_msg": "{cal} <b>Выберите год аккаунта</b>\n{globe} Страна: <b>{country}</b>\n\n",
        "confirm_buy_msg": "{cart} <b>Подтвердите покупку</b>\n\n{flag} <b>Страна:</b> {country}\n{cal} <b>Год:</b> {year}\n{pts} <b>Итоговая цена:</b> <b>{price} Pts</b> (${usd_price:.2f})\n\n{card} <b>Ваш баланс:</b> <b>{bal} Pts</b>\n\n❓ Продолжить покупку?",
        "sold_out_alert": "❌ Товар закончился! Другой пользователь уже купил этот аккаунт.",
        "insufficient_bal_alert": "❌ Недостаточно средств! Нужно {price} Pts",
        "insufficient_bal_msg": "{no} <b>Недостаточно средств!</b>\nДля покупки {qty} сессий нужно <b>{cost} Pts</b>.",
        "fetching_num": "🔄 <b>Получаем номер (+{phone})...</b>",
        "acc_invalid": "{no} <b>Аккаунт недействителен.</b> Поинты возвращены. Попробуйте другой.",
        "order_active_msg": "{yes} <b>Заказ активен!</b>\n\n{phone_e} <b>Телефон:</b> <code>{phone}</code>\n{flag} <b>Страна:</b> {c_icon} {country}\n\n🔻 <b>ИНСТРУКЦИЯ:</b>\n1. Откройте Telegram и нажмите «Добавить аккаунт»\n2. Введите номер выше.\n3. {wait} <b>Подождите!</b> Бот ожидает код и отправит его автоматически.\n\n<i>Примечание: если код не придёт за 10 минут, заказ отменится, а поинты вернутся автоматически.</i>",
        "otp_fetched_msg": "{yes} <b>Получен свежий код!</b>\n\n{phone_e} <b>Телефон:</b> <code>{phone}</code>\n{flag} <b>Страна:</b> {c_icon} {country}\n{otp_e} <b>Код:</b> <code>{code}</code>\n{twofa_line}",
        "twofa_enabled": "{twofa} <b>2FA:</b> <code>{pwd}</code>",
        "twofa_disabled": "🔓 <b>2FA:</b> <code>Отключена (без пароля)</code>",
        "order_expired_msg": "{time_e} <b>Время заказа истекло!</b>\nЛимит 10 минут для <code>{phone}</code> вышел. Ваши <b>{price} Pts</b> автоматически возвращены.",
        "session_logged_out_alert": "⚠️ Сессия уже завершена или истекла.",
        "fetching_otp_toast": "🔄 Проверяем новый код...",
        "no_new_otp_alert": "⏳ Новый код ещё не пришёл. Попробуйте через несколько секунд.",
        "otp_err_alert": "❌ Ошибка при получении кода.",
        "session_finished_msg": "{yes} <b>Сессия завершена и выход выполнен.</b>",
        "no_active_order_alert": "⚠️ Активный заказ не найден.",
        "bulk_prompt_msg": "{store} <b>Покупка сессий {country} ({year})</b>\n\n{pts} <b>Цена за сессию:</b> <b>{price} Pts</b>\n{pkg} <b>Доступно:</b> {stock}\n\n👇 Ответьте на это сообщение, указав <b>количество сессий</b>.",
        "not_enough_stock_msg": "{warn} <b>Недостаточно товара!</b> Максимум: {stock}.",
        "enter_valid_num_msg": "{no} Введите корректное число.",
        "processing_sessions_msg": "{wait} <b>Формируем архив сессий...</b>",
        "stock_changed_msg": "{no} Наличие изменилось во время обработки. Покупка отменена.",
        "bulk_success_caption": "{yes} <b>Массовая покупка выполнена!</b>\n\n{flag} Страна: {country}\n{pkg} Количество: {qty}\n{pts} Оплачено: <b>{cost} Pts</b>\n\n<i>(Сессии переданы, бот не удерживает их активными)</i>",
        "zip_err_msg": "{warn} Ошибка создания архива: {err}",
        "support_msg": "{on} <b>Поддержка и информация Fresh Tg</b>\n\n{warn} По вопросам обращайтесь к администратору..",
        "btn_support_url": "📩 Поддержка",
        "btn_terms_url": "📜 Правила и условия",
        "btn_channel_url": "📢 Канал",
        "dep_group_unavail": "{warn} <b>Группа пополнения не настроена</b>\nОбратитесь в поддержку.",
        "dep_menu_msg": "{money} <b>ПОПОЛНЕНИЕ USDT (АВТО-ПОИНТЫ)</b>\n━━━━━━━━━━━━━━━━━━━━━━\n{pts} <b>Курс:</b> <code>$1 USDT = {rate} Points</code>\n{asst} <b>Бот типсов:</b> <code>@{tip_bot}</code>\n{acc} <b>Получатель:</b> <code>@{receiver}</code>\n\n<b>Как пополнить:</b>\n1. Вступите в группу пополнения по кнопке ниже.\n2. Отправьте команду (или ответьте на сообщение получателя):\n   <code>cc (amount) usdt @{receiver}</code>\n3. После подтверждения от <code>@{tip_bot}</code> поинты зачислятся автоматически, и через 5 секунд вы будете удалены из группы.\n\n{warn} <b>Важно:</b>\n• Пополнения меньше <b>0.5 USDT</b> <b>не учитываются</b>. Если вы отправили меньше 0.5 USDT, обратитесь в поддержку.\n• Если не отправить сообщение в течение <b>2 минут</b> после входа, бот удалит вас из группы.",
        "grp_welcome_msg": "{spark} <b>ИНСТРУКЦИЯ ПО ПОПОЛНЕНИЮ</b> — {mention}\n━━━━━━━━━━━━━━━━━━━━━━\n{money} Отправьте тип (напрямую или ответом на сообщение получателя):\n<code>cc (deposit amount) usdt @{receiver}</code>\n<i>Пример:</i> <code>cc 5 usdt @{receiver}</code>\n\n{pts} <b>Курс:</b> <code>$1 USDT = {rate} Points</code>\n\n{warn} <b>Важные правила:</b>\n• Депозиты ниже <b>0.5 USDT</b> <b>не засчитываются</b>. При отправке менее 0.5 USDT обратитесь в поддержку.\n• Отправьте сообщение в течение <b>2 минут</b>, иначе вы будете исключены.",
        "grp_inactive_kick": "{time_e} <a href='tg://user?id={uid}'>Участник</a> исключён за 2 минуты бездействия.",
        "grp_wrong_token": "{warn} <a href='tg://user?id={uid}'>Участник</a>, обнаружен неподдерживаемый токен.\nАвтоматически зачисляется только <b>USDT</b>—обратитесь в <b>Поддержку</b>.",
        "grp_wrong_token_anon": "{warn} Обнаружен неподдерживаемый токен. Зачисляется только <b>USDT</b>—обратитесь в <b>Поддержку</b>.",
        "grp_min_warn": "{warn} <a href='tg://user?id={uid}'>Участник</a>, сумма <b>{amt} USDT</b> меньше минимума <b>0.5 USDT</b>.\nДепозиты ниже <b>0.5 USDT</b> не засчитываются—обратитесь в <b>Поддержку</b>.",
        "grp_confirmed": "{yes} <a href='tg://user?id={uid}'>Депозит подтверждён</a> — начислено <b>+{pts} Points</b> (${amt:.2f} USDT).\n<i>Удаляем из группы через 5 секунд...</i>",
        "dm_deposit_credited": "{yes} Депозит зачислен — на ваш баланс добавлено <b>{pts} Points</b> (${amt:.2f} USDT).\n{pts} Новый баланс: <b>{bal} Points</b> | Курс: $1 = {rate} Points.",
    },
    "es": {
        "choose_lang_title": "🌐 <b>Elige tu idioma</b>",
        "choose_lang_desc": "Selecciona el idioma que deseas usar en el bot.",
        "lang_updated": "✅ ¡Idioma cambiado a <b>Español</b>!",
        "lang_set_continue": "✅ ¡Idioma configurado en <b>Español</b>!",
        "btn_language": "Idioma",
        "btn_buy_account": "Comprar Cuenta",
        "btn_my_profile": "Mi Perfil",
        "btn_buy_sessions": "Comprar Sesiones",
        "btn_deposit": "Depositar",
        "btn_my_stats": "Mis Estadísticas",
        "btn_support": "Soporte",
        "btn_admin_panel": "Panel Admin",
        "btn_choose_lang": "🌐 Idioma / Language",
        "btn_join_ch": "📢 Unirse al Canal ({title})",
        "btn_verify_join": "✅ Verificar Unión",
        "btn_read_terms": "📜 Leer Términos y Condiciones",
        "btn_accept": "✅ Aceptar",
        "btn_reject": "❌ Rechazar",
        "btn_cancel": "❌ Cancelar",
        "btn_back": "🔙 Atrás",
        "btn_prev": "⬅️ Ant.",
        "btn_next": "➡️ Sig.",
        "btn_buy_now": "✅ Sí, comprar ahora",
        "btn_get_otp_again": "🔄 Obtener OTP de nuevo",
        "btn_logout": "🚪 Finalizar y cerrar sesión",
        "btn_purchase_logs": "📜 Historial de compras",
        "btn_referral_logs": "👥 Referidos",
        "btn_join_dep_grp": "🏦 Unirse al Grupo de Depósito",
        "btn_contact_support": "📩 Contactar Soporte",
        "bot_maintenance": "{off} <b>El bot está en mantenimiento.</b> Inténtalo más tarde.",
        "bot_maintenance_alert": "⚙️ El bot está en mantenimiento.",
        "slow_down": "⚠️ ¡Ve más despacio! No hagas spam en los botones.",
        "banned_alert": "🚫 BANEADO",
        "force_join_msg": "{warn} <b>¡Debes unirte primero a nuestros canales!</b>",
        "must_join_alert": "⚠️ ¡Primero debes unirte a los canales!",
        "terms_msg": "{doc} <b>TÉRMINOS Y CONDICIONES</b>\nPor favor lee y acepta los Términos y Condiciones antes de usar el bot.",
        "terms_accepted_alert": "✅ ¡Términos aceptados!",
        "terms_rejected_msg": "{no} No puedes usar el bot sin aceptar los términos.",
        "cancelled_msg": "{no} <b>Cancelado.</b>",
        "welcome_msg": "👋 <b>¡Bienvenido a Fresh Tg Store!</b>\n\n{pts} <b>Tasa:</b> <code>$1 USDT = {rate} Points</code>\n{gift} <b>Invita y gana:</b>\n¡Invita amigos y gana el {pct}% de sus depósitos en Points!\n{globe} <code>https://t.me/{bot_user}?start=ref_{ref_uid}</code>",
        "init_error": "⚠️ Error: escribe /start para inicializar tu cuenta.",
        "profile_msg": "{acc} <b>PERFIL DE USUARIO</b>\n\n{id_e} ID de usuario: <code>{uid}</code>\n{pts} Saldo: <code>{bal} Pts (${usd_bal:.2f})</code>\n{card} Depositado: <code>{dep} Pts (${usd_dep:.2f})</code>{disc_msg}\n{cal} Registro: {joined}\n\n{users} <b>Tu enlace de referido:</b>\n<code>{ref_link}</code>\n\n<i>(¡Comparte este enlace con tus amigos para ganar puntos!)</i>",
        "active_discount": "\n{gift} Descuento activo: <b>{discount}% OFF</b>",
        "stats_msg": "{stats} <b>Mis Estadísticas</b>\n\n{cart} <b>Cuentas compradas:</b> {orders}\n{pts} <b>Total gastado:</b> {spent} Pts (${usd_spent:.2f})\n{card} <b>Total depositado:</b> {dep} Pts (${usd_dep:.2f})",
        "ref_count_alert": "👥 Has referido a {count} usuario(s).",
        "purchase_hist_title": "{doc} <b>Historial de compras (Pág. {page})</b>\n\n",
        "no_purchases": "No se encontraron compras.",
        "stock_empty": "{no} <b>El stock está vacío por ahora. ¡Vuelve más tarde!</b>",
        "bulk_menu": "{store} <b>Menú de Sesiones Masivas</b>",
        "single_menu": "{cart} <b>Menú de Cuenta Individual</b>",
        "select_region": "{title}\n\n{globe} <b>Selecciona una región para ver números disponibles (Pág. {page}).</b>\n{usdt} Tasa: $1 USDT = <b>{rate} Points</b>\n\n",
        "out_of_stock_alert": "❌ Agotado para este país.",
        "out_of_stock_short": "❌ ¡Agotado!",
        "select_year_msg": "{cal} <b>Selecciona el año de la cuenta</b>\n{globe} País: <b>{country}</b>\n\n",
        "confirm_buy_msg": "{cart} <b>Confirma tu compra</b>\n\n{flag} <b>País:</b> {country}\n{cal} <b>Año:</b> {year}\n{pts} <b>Precio final:</b> <b>{price} Pts</b> (${usd_price:.2f})\n\n{card} <b>Tu saldo:</b> <b>{bal} Pts</b>\n\n❓ ¿Deseas continuar con esta compra?",
        "sold_out_alert": "❌ ¡Agotado! Otro usuario acaba de comprar esta cuenta.",
        "insufficient_bal_alert": "❌ ¡Saldo insuficiente! Necesitas {price} Pts",
        "insufficient_bal_msg": "{no} <b>¡Saldo insuficiente!</b>\nNecesitas <b>{cost} Pts</b> para comprar {qty} sesiones.",
        "fetching_num": "🔄 <b>Obteniendo número (+{phone})...</b>",
        "acc_invalid": "{no} <b>Cuenta inválida.</b> Points reembolsados. Intenta con otra.",
        "order_active_msg": "{yes} <b>¡Pedido activo!</b>\n\n{phone_e} <b>Teléfono:</b> <code>{phone}</code>\n{flag} <b>País:</b> {c_icon} {country}\n\n🔻 <b>INSTRUCCIONES:</b>\n1. Abre Telegram y Añadir cuenta\n2. Ingresa el número de arriba.\n3. {wait} <b>¡Espera!</b> El bot escucha tu OTP y lo enviará automáticamente.\n\n<i>Nota: si no llega OTP en 10 minutos, se cancelará y reembolsará automáticamente.</i>",
        "otp_fetched_msg": "{yes} <b>¡Último OTP obtenido!</b>\n\n{phone_e} <b>Teléfono:</b> <code>{phone}</code>\n{flag} <b>País:</b> {c_icon} {country}\n{otp_e} <b>OTP:</b> <code>{code}</code>\n{twofa_line}",
        "twofa_enabled": "{twofa} <b>2FA:</b> <code>{pwd}</code>",
        "twofa_disabled": "🔓 <b>2FA:</b> <code>Desactivada (Sin contraseña)</code>",
        "order_expired_msg": "{time_e} <b>¡Pedido expirado!</b>\nSe agotó el límite de 10 minutos para <code>{phone}</code>. Tus <b>{price} Pts</b> fueron reembolsados.",
        "session_logged_out_alert": "⚠️ La sesión ya cerró o expiró.",
        "fetching_otp_toast": "🔄 Buscando OTP más reciente...",
        "no_new_otp_alert": "⏳ Aún no hay un nuevo OTP. Intenta en unos segundos.",
        "otp_err_alert": "❌ Error al obtener OTP.",
        "session_finished_msg": "{yes} <b>Sesión finalizada y cerrada correctamente.</b>",
        "no_active_order_alert": "⚠️ No hay un pedido activo.",
        "bulk_prompt_msg": "{store} <b>Comprar sesiones de {country} ({year})</b>\n\n{pts} <b>Precio por sesión:</b> <b>{price} Pts</b>\n{pkg} <b>Stock disponible:</b> {stock}\n\n👇 <b>Responde a este mensaje</b> con la <b>cantidad de sesiones</b> que deseas comprar.",
        "not_enough_stock_msg": "{warn} <b>¡No hay suficiente stock!</b> Máximo: {stock}.",
        "enter_valid_num_msg": "{no} Ingresa un número válido.",
        "processing_sessions_msg": "{wait} <b>Procesando tus sesiones...</b>",
        "stock_changed_msg": "{no} El stock cambió durante el proceso. Compra cancelada.",
        "bulk_success_caption": "{yes} <b>¡Compra masiva exitosa!</b>\n\n{flag} País: {country}\n{pkg} Cantidad: {qty}\n{pts} Total pagado: <b>{cost} Pts</b>\n\n<i>(Las sesiones se entregan de forma segura, el bot no las mantiene activas)</i>",
        "zip_err_msg": "{warn} Error al crear ZIP: {err}",
        "support_msg": "{on} <b>Soporte e información de Fresh Tg</b>\n\n{warn} Para soporte contacta al administrador..",
        "btn_support_url": "📩 Soporte",
        "btn_terms_url": "📜 Términos y Condiciones",
        "btn_channel_url": "📢 Canal",
        "dep_group_unavail": "{warn} <b>Grupo de depósito no disponible</b>\nContacta a Soporte.",
        "dep_menu_msg": "{money} <b>PORTAL DE DEPÓSITO USDT (AUTO POINTS)</b>\n━━━━━━━━━━━━━━━━━━━━━━\n{pts} <b>Tasa:</b> <code>$1 USDT = {rate} Points</code>\n{asst} <b>Procesador:</b> <code>@{tip_bot}</code>\n{acc} <b>Destinatario:</b> <code>@{receiver}</code>\n\n<b>Cómo depositar:</b>\n1. Únete al Grupo de Depósito con el botón de abajo.\n2. Envía tu propina (directo o respondiendo al destinatario):\n   <code>cc (amount) usdt @{receiver}</code>\n3. Cuando <code>@{tip_bot}</code> confirme la propina, se acreditarán los Points y saldrás del grupo en 5 segundos.\n\n{warn} <b>Aviso importante:</b>\n• Depósitos menores a <b>0.5 USDT</b> <b>no</b> se contarán. Si enviaste menos de 0.5 USDT, contacta a Soporte.\n• Si no envías un mensaje en <b>2 minutos</b> tras entrar, serás eliminado automáticamente.",
        "grp_welcome_msg": "{spark} <b>INSTRUCCIONES DE DEPÓSITO</b> — {mention}\n━━━━━━━━━━━━━━━━━━━━━━\n{money} Envía tu propina (directo o respondiendo al destinatario):\n<code>cc (deposit amount) usdt @{receiver}</code>\n<i>Ejemplo:</i> <code>cc 5 usdt @{receiver}</code>\n\n{pts} <b>Tasa:</b> <code>$1 USDT = {rate} Points</code>\n\n{warn} <b>Reglas importantes:</b>\n• Depósitos menores a <b>0.5 USDT</b> <b>no</b> se contarán. Si enviaste menos de 0.5 USDT, contacta a Soporte.\n• Envía un mensaje dentro de <b>2 minutos</b> o serás expulsado automáticamente.",
        "grp_inactive_kick": "{time_e} <a href='tg://user?id={uid}'>Usuario</a> eliminado por 2 minutos de inactividad.",
        "grp_wrong_token": "{warn} <a href='tg://user?id={uid}'>Usuario</a>, token no compatible detectado en tu propina.\nSolo se acreditan automáticamente depósitos en <b>USDT</b>—contacta a <b>Soporte</b>.",
        "grp_wrong_token_anon": "{warn} Token no compatible detectado. Solo se acreditan depósitos en <b>USDT</b>—contacta a <b>Soporte</b>.",
        "grp_min_warn": "{warn} <a href='tg://user?id={uid}'>Usuario</a>, tu depósito de <b>{amt} USDT</b> es menor al mínimo de <b>0.5 USDT</b>.\nDepósitos menores a <b>0.5 USDT</b> no se cuentan—contacta a <b>Soporte</b> si ya pagaste.",
        "grp_confirmed": "{yes} <a href='tg://user?id={uid}'>Depósito confirmado</a> — <b>+{pts} Points</b> (${amt:.2f} USDT) acreditados.\n<i>Saliendo del grupo en 5 segundos...</i>",
        "dm_deposit_credited": "{yes} Depósito acreditado — se añadieron <b>{pts} Points</b> (${amt:.2f} USDT) a tu cuenta.\n{pts} Nuevo saldo: <b>{bal} Points</b> | Tasa: $1 = {rate} Points.",
    },
    "fr": {
        "choose_lang_title": "🌐 <b>Choisissez votre langue</b>",
        "choose_lang_desc": "Sélectionnez la langue à utiliser dans le bot.",
        "lang_updated": "✅ Langue mise à jour : <b>Français</b> !",
        "lang_set_continue": "✅ Langue définie sur <b>Français</b> !",
        "btn_language": "Langue",
        "btn_buy_account": "Acheter un compte",
        "btn_my_profile": "Mon profil",
        "btn_buy_sessions": "Acheter sessions",
        "btn_deposit": "Dépôt",
        "btn_my_stats": "Mes statistiques",
        "btn_support": "Support",
        "btn_admin_panel": "Panneau Admin",
        "btn_choose_lang": "🌐 Langue / Language",
        "btn_join_ch": "📢 Rejoindre ({title})",
        "btn_verify_join": "✅ Vérifier l'adhésion",
        "btn_read_terms": "📜 Lire les Conditions",
        "btn_accept": "✅ Accepter",
        "btn_reject": "❌ Refuser",
        "btn_cancel": "❌ Annuler",
        "btn_back": "🔙 Retour",
        "btn_prev": "⬅️ Préc.",
        "btn_next": "➡️ Suiv.",
        "btn_buy_now": "✅ Oui, acheter maintenant",
        "btn_get_otp_again": "🔄 Recevoir le code à nouveau",
        "btn_logout": "🚪 Terminer et déconnecter",
        "btn_purchase_logs": "📜 Historique d'achats",
        "btn_referral_logs": "👥 Parrainages",
        "btn_join_dep_grp": "🏦 Groupe de dépôt",
        "btn_contact_support": "📩 Contacter le Support",
        "bot_maintenance": "{off} <b>Le bot est en maintenance.</b> Veuillez réessayer plus tard.",
        "bot_maintenance_alert": "⚙️ Bot en maintenance.",
        "slow_down": "⚠️ Ralentissez ! N'appuyez pas trop vite.",
        "banned_alert": "🚫 BANNI",
        "force_join_msg": "{warn} <b>Vous devez d'abord rejoindre nos canaux !</b>",
        "must_join_alert": "⚠️ Vous devez d'abord rejoindre les canaux !",
        "terms_msg": "{doc} <b>CONDITIONS GÉNÉRALES</b>\nVeuillez lire et accepter les conditions avant d'utiliser le bot.",
        "terms_accepted_alert": "✅ Conditions acceptées !",
        "terms_rejected_msg": "{no} Vous ne pouvez pas utiliser le bot sans accepter les conditions.",
        "cancelled_msg": "{no} <b>Annulé.</b>",
        "welcome_msg": "👋 <b>Bienvenue sur Fresh Tg Store !</b>\n\n{pts} <b>Taux :</b> <code>$1 USDT = {rate} Points</code>\n{gift} <b>Parrainage :</b>\nInvitez des amis et gagnez {pct}% de leurs dépôts en Points !\n{globe} <code>https://t.me/{bot_user}?start=ref_{ref_uid}</code>",
        "init_error": "⚠️ Erreur : tapez /start pour initialiser votre compte.",
        "profile_msg": "{acc} <b>PROFIL UTILISATEUR</b>\n\n{id_e} ID utilisateur : <code>{uid}</code>\n{pts} Solde : <code>{bal} Pts (${usd_bal:.2f})</code>\n{card} Déposé : <code>{dep} Pts (${usd_dep:.2f})</code>{disc_msg}\n{cal} Inscrit : {joined}\n\n{users} <b>Votre lien de parrainage :</b>\n<code>{ref_link}</code>\n\n<i>(Partagez ce lien pour gagner des bonus en Points !)</i>",
        "active_discount": "\n{gift} Réduction active : <b>{discount}% OFF</b>",
        "stats_msg": "{stats} <b>Mes Statistiques</b>\n\n{cart} <b>Comptes achetés :</b> {orders}\n{pts} <b>Total dépensé :</b> {spent} Pts (${usd_spent:.2f})\n{card} <b>Total déposé :</b> {dep} Pts (${usd_dep:.2f})",
        "ref_count_alert": "👥 Vous avez parrainé {count} utilisateur(s).",
        "purchase_hist_title": "{doc} <b>Historique des achats (Page {page})</b>\n\n",
        "no_purchases": "Aucun achat trouvé.",
        "stock_empty": "{no} <b>Le stock est vide pour le moment. Revenez plus tard !</b>",
        "bulk_menu": "{store} <b>Menu Sessions en Gros</b>",
        "single_menu": "{cart} <b>Menu Compte Unique</b>",
        "select_region": "{title}\n\n{globe} <b>Choisissez une région pour voir les numéros (Page {page}).</b>\n{usdt} Taux : $1 USDT = <b>{rate} Points</b>\n\n",
        "out_of_stock_alert": "❌ Rupture de stock pour ce pays.",
        "out_of_stock_short": "❌ Rupture de stock !",
        "select_year_msg": "{cal} <b>Choisissez l'année du compte</b>\n{globe} Pays : <b>{country}</b>\n\n",
        "confirm_buy_msg": "{cart} <b>Confirmez votre achat</b>\n\n{flag} <b>Pays :</b> {country}\n{cal} <b>Année :</b> {year}\n{pts} <b>Prix final :</b> <b>{price} Pts</b> (${usd_price:.2f})\n\n{card} <b>Votre solde :</b> <b>{bal} Pts</b>\n\n❓ Voulez-vous continuer cet achat ?",
        "sold_out_alert": "❌ Épuisé ! Un autre utilisateur vient d'acheter ce compte.",
        "insufficient_bal_alert": "❌ Solde insuffisant ! {price} Pts requis",
        "insufficient_bal_msg": "{no} <b>Solde insuffisant !</b>\nIl vous faut <b>{cost} Pts</b> pour {qty} sessions.",
        "fetching_num": "🔄 <b>Récupération du numéro (+{phone})...</b>",
        "acc_invalid": "{no} <b>Compte invalide.</b> Points remboursés. Essayez un autre.",
        "order_active_msg": "{yes} <b>Commande active !</b>\n\n{phone_e} <b>Téléphone :</b> <code>{phone}</code>\n{flag} <b>Pays :</b> {c_icon} {country}\n\n🔻 <b>INSTRUCTIONS :</b>\n1. Ouvrez Telegram et Ajoutez un compte\n2. Entrez le numéro ci-dessus.\n3. {wait} <b>Patientez !</b> Le bot attend votre code et l'enverra automatiquement.\n\n<i>Si aucun code n'arrive en 10 minutes, la commande est annulée et remboursée.</i>",
        "otp_fetched_msg": "{yes} <b>Dernier code reçu !</b>\n\n{phone_e} <b>Téléphone :</b> <code>{phone}</code>\n{flag} <b>Pays :</b> {c_icon} {country}\n{otp_e} <b>OTP :</b> <code>{code}</code>\n{twofa_line}",
        "twofa_enabled": "{twofa} <b>2FA :</b> <code>{pwd}</code>",
        "twofa_disabled": "🔓 <b>2FA :</b> <code>Désactivée (Aucun mot de passe)</code>",
        "order_expired_msg": "{time_e} <b>Commande expirée !</b>\nDélai de 10 minutes dépassé pour <code>{phone}</code>. Vos <b>{price} Pts</b> ont été remboursés.",
        "session_logged_out_alert": "⚠️ Session déjà déconnectée ou expirée.",
        "fetching_otp_toast": "🔄 Récupération du code...",
        "no_new_otp_alert": "⏳ Aucun nouveau code pour l'instant. Réessayez dans quelques secondes.",
        "otp_err_alert": "❌ Erreur lors de la récupération du code.",
        "session_finished_msg": "{yes} <b>Session terminée et déconnectée.</b>",
        "no_active_order_alert": "⚠️ Aucune commande active.",
        "bulk_prompt_msg": "{store} <b>Acheter des sessions {country} ({year})</b>\n\n{pts} <b>Prix par session :</b> <b>{price} Pts</b>\n{pkg} <b>Stock disponible :</b> {stock}\n\n👇 <b>Répondez à ce message</b> avec le <b>nombre de sessions</b> souhaité.",
        "not_enough_stock_msg": "{warn} <b>Stock insuffisant !</b> Maximum : {stock}.",
        "enter_valid_num_msg": "{no} Entrez un nombre valide.",
        "processing_sessions_msg": "{wait} <b>Traitement de vos sessions...</b>",
        "stock_changed_msg": "{no} Le stock a changé. Achat annulé.",
        "bulk_success_caption": "{yes} <b>Achat groupé réussi !</b>\n\n{flag} Pays : {country}\n{pkg} Quantité : {qty}\n{pts} Total payé : <b>{cost} Pts</b>\n\n<i>(Sessions fournies en toute sécurité, le bot ne les garde pas actives)</i>",
        "zip_err_msg": "{warn} Erreur ZIP : {err}",
        "support_msg": "{on} <b>Support et informations Fresh Tg</b>\n\n{warn} Pour toute aide, contactez l'administrateur..",
        "btn_support_url": "📩 Support",
        "btn_terms_url": "📜 Conditions",
        "btn_channel_url": "📢 Canal",
        "dep_group_unavail": "{warn} <b>Groupe de dépôt indisponible</b>\nContactez le Support.",
        "dep_menu_msg": "{money} <b>PORTAIL DE DÉPÔT USDT (AUTO POINTS)</b>\n━━━━━━━━━━━━━━━━━━━━━━\n{pts} <b>Taux :</b> <code>$1 USDT = {rate} Points</code>\n{asst} <b>Processeur :</b> <code>@{tip_bot}</code>\n{acc} <b>Destinataire :</b> <code>@{receiver}</code>\n\n<b>Comment déposer :</b>\n1. Rejoignez le groupe de dépôt via le bouton ci-dessous.\n2. Envoyez votre tip (directement ou en réponse au destinataire) :\n   <code>cc (amount) usdt @{receiver}</code>\n3. Dès que <code>@{tip_bot}</code> confirme, les Points sont crédités et vous êtes retiré du groupe en 5 secondes.\n\n{warn} <b>Important :</b>\n• Les dépôts sous <b>0.5 USDT</b> ne sont <b>pas</b> comptabilisés. Contactez le Support si besoin.\n• Aucun message en <b>2 minutes</b> après l'entrée entraîne une exclusion automatique.",
        "grp_welcome_msg": "{spark} <b>INSTRUCTIONS DE DÉPÔT</b> — {mention}\n━━━━━━━━━━━━━━━━━━━━━━\n{money} Envoyez votre tip (directement ou en réponse au destinataire) :\n<code>cc (deposit amount) usdt @{receiver}</code>\n<i>Exemple :</i> <code>cc 5 usdt @{receiver}</code>\n\n{pts} <b>Taux :</b> <code>$1 USDT = {rate} Points</code>\n\n{warn} <b>Règles importantes :</b>\n• Les dépôts sous <b>0.5 USDT</b> ne sont <b>pas</b> comptabilisés. Contactez le Support si besoin.\n• Envoyez un message dans les <b>2 minutes</b> sinon vous serez retiré.",
        "grp_inactive_kick": "{time_e} <a href='tg://user?id={uid}'>Membre</a> retiré après 2 minutes d'inactivité.",
        "grp_wrong_token": "{warn} <a href='tg://user?id={uid}'>Membre</a>, jeton non pris en charge.\nSeuls les dépôts <b>USDT</b> sont crédités automatiquement—contactez le <b>Support</b>.",
        "grp_wrong_token_anon": "{warn} Jeton non pris en charge. Seuls les dépôts <b>USDT</b> sont crédités—contactez le <b>Support</b>.",
        "grp_min_warn": "{warn} <a href='tg://user?id={uid}'>Membre</a>, votre dépôt de <b>{amt} USDT</b> est sous le minimum de <b>0.5 USDT</b>.\nLes dépôts sous <b>0.5 USDT</b> ne sont pas comptabilisés—contactez le <b>Support</b>.",
        "grp_confirmed": "{yes} <a href='tg://user?id={uid}'>Dépôt confirmé</a> — <b>+{pts} Points</b> (${amt:.2f} USDT) crédités.\n<i>Retrait du groupe dans 5 secondes...</i>",
        "dm_deposit_credited": "{yes} Dépôt crédité — <b>{pts} Points</b> (${amt:.2f} USDT) ajoutés à votre compte.\n{pts} Nouveau solde : <b>{bal} Points</b> | Taux : $1 = {rate} Points.",
    },
    "ar": {
        "choose_lang_title": "🌐 <b>اختر لغتك</b>",
        "choose_lang_desc": "اختر اللغة التي تريد استخدامها في البوت.",
        "lang_updated": "✅ تم تغيير اللغة إلى <b>العربية</b>!",
        "lang_set_continue": "✅ تم ضبط اللغة على <b>العربية</b>!",
        "btn_language": "اللغة",
        "btn_buy_account": "شراء حساب",
        "btn_my_profile": "ملفي الشخصي",
        "btn_buy_sessions": "شراء جلسات",
        "btn_deposit": "إيداع",
        "btn_my_stats": "إحصائياتي",
        "btn_support": "الدعم",
        "btn_admin_panel": "لوحة الأدمن",
        "btn_choose_lang": "🌐 اللغة / Language",
        "btn_join_ch": "📢 انضم للقناة ({title})",
        "btn_verify_join": "✅ تحقق من الانضمام",
        "btn_read_terms": "📜 قراءة الشروط والأحكام",
        "btn_accept": "✅ موافق",
        "btn_reject": "❌ رفض",
        "btn_cancel": "❌ إلغاء",
        "btn_back": "🔙 رجوع",
        "btn_prev": "⬅️ السابق",
        "btn_next": "➡️ التالي",
        "btn_buy_now": "✅ نعم، اشترِ الآن",
        "btn_get_otp_again": "🔄 جلب الرمز مرة أخرى",
        "btn_logout": "🚪 إنهاء وتسجيل الخروج",
        "btn_purchase_logs": "📜 سجل المشتريات",
        "btn_referral_logs": "👥 الإحالات",
        "btn_join_dep_grp": "🏦 مجموعة الإيداع",
        "btn_contact_support": "📩 تواصل مع الدعم",
        "bot_maintenance": "{off} <b>البوت قيد الصيانة حالياً.</b> يرجى المحاولة لاحقاً.",
        "bot_maintenance_alert": "⚙️ البوت قيد الصيانة.",
        "slow_down": "⚠️ يرجى التمهل وعدم الضغط المتكرر على الأزرار.",
        "banned_alert": "🚫 محظور",
        "force_join_msg": "{warn} <b>يجب الانضمام إلى قنواتنا أولاً!</b>",
        "must_join_alert": "⚠️ يجب الانضمام إلى القنوات أولاً!",
        "terms_msg": "{doc} <b>الشروط والأحكام</b>\nيرجى قراءة الشروط والأحكام والموافقة عليها قبل استخدام البوت.",
        "terms_accepted_alert": "✅ تمت الموافقة على الشروط!",
        "terms_rejected_msg": "{no} لا يمكنك استخدام البوت دون الموافقة على الشروط.",
        "cancelled_msg": "{no} <b>تم الإلغاء.</b>",
        "welcome_msg": "👋 <b>مرحباً بك في Fresh Tg Store!</b>\n\n{pts} <b>سعر الصرف:</b> <code>$1 USDT = {rate} Points</code>\n{gift} <b>ادعُ واربح:</b>\nادعُ أصدقاءك واربح {pct}% من إيداعاتهم بالنقاط!\n{globe} <code>https://t.me/{bot_user}?start=ref_{ref_uid}</code>",
        "init_error": "⚠️ خطأ: اكتب /start لتهيئة حسابك.",
        "profile_msg": "{acc} <b>الملف الشخصي</b>\n\n{id_e} معرف المستخدم: <code>{uid}</code>\n{pts} الرصيد: <code>{bal} Pts (${usd_bal:.2f})</code>\n{card} الإيداعات: <code>{dep} Pts (${usd_dep:.2f})</code>{disc_msg}\n{cal} تاريخ الانضمام: {joined}\n\n{users} <b>رابط الإحالة الخاص بك:</b>\n<code>{ref_link}</code>\n\n<i>(شارك الرابط مع أصدقائك لكسب نقاط إضافية!)</i>",
        "active_discount": "\n{gift} خصم نشط: <b>{discount}% OFF</b>",
        "stats_msg": "{stats} <b>إحصائياتي</b>\n\n{cart} <b>الحسابات المشتراة:</b> {orders}\n{pts} <b>إجمالي الإنفاق:</b> {spent} Pts (${usd_spent:.2f})\n{card} <b>إجمالي الإيداع:</b> {dep} Pts (${usd_dep:.2f})",
        "ref_count_alert": "👥 لقد قمت بإحالة {count} مستخدم.",
        "purchase_hist_title": "{doc} <b>سجل المشتريات (صفحة {page})</b>\n\n",
        "no_purchases": "لا توجد مشتريات.",
        "stock_empty": "{no} <b>المخزون فارغ حالياً. عد لاحقاً!</b>",
        "bulk_menu": "{store} <b>قائمة الجلسات بالجملة</b>",
        "single_menu": "{cart} <b>قائمة الحساب الفردي</b>",
        "select_region": "{title}\n\n{globe} <b>اختر الدولة لعرض الأرقام المتاحة (صفحة {page}).</b>\n{usdt} السعر: $1 USDT = <b>{rate} Points</b>\n\n",
        "out_of_stock_alert": "❌ نفدت الكمية لهذه الدولة.",
        "out_of_stock_short": "❌ نفد المخزون!",
        "select_year_msg": "{cal} <b>اختر سنة الحساب</b>\n{globe} الدولة: <b>{country}</b>\n\n",
        "confirm_buy_msg": "{cart} <b>تأكيد الشراء</b>\n\n{flag} <b>الدولة:</b> {country}\n{cal} <b>السنة:</b> {year}\n{pts} <b>السعر النهائي:</b> <b>{price} Pts</b> (${usd_price:.2f})\n\n{card} <b>رصيدك:</b> <b>{bal} Pts</b>\n\n❓ هل تريد متابعة الشراء؟",
        "sold_out_alert": "❌ نفد الحساب! قام مستخدم آخر بشرائه.",
        "insufficient_bal_alert": "❌ الرصيد غير كافٍ! مطلوب {price} Pts",
        "insufficient_bal_msg": "{no} <b>الرصيد غير كافٍ!</b>\nتحتاج إلى <b>{cost} Pts</b> لشراء {qty} جلسات.",
        "fetching_num": "🔄 <b>جاري جلب الرقم (+{phone})...</b>",
        "acc_invalid": "{no} <b>الحساب غير صالح.</b> تم إرجاع النقاط. جرب حساباً آخر.",
        "order_active_msg": "{yes} <b>الطلب نشط!</b>\n\n{phone_e} <b>الهاتف:</b> <code>{phone}</code>\n{flag} <b>الدولة:</b> {c_icon} {country}\n\n🔻 <b>التعليمات:</b>\n1. افتح تيليجرام واختر إضافة حساب\n2. أدخل الرقم أعلاه.\n3. {wait} <b>يرجى الانتظار!</b> يراقب البوت رمز OTP وسيرسله تلقائياً.\n\n<i>ملاحظة: إذا لم يصل الرمز خلال 10 دقائق فسيتم إلغاء الطلب واسترداد النقاط تلقائياً.</i>",
        "otp_fetched_msg": "{yes} <b>تم جلب أحدث رمز OTP!</b>\n\n{phone_e} <b>الهاتف:</b> <code>{phone}</code>\n{flag} <b>الدولة:</b> {c_icon} {country}\n{otp_e} <b>OTP:</b> <code>{code}</code>\n{twofa_line}",
        "twofa_enabled": "{twofa} <b>2FA:</b> <code>{pwd}</code>",
        "twofa_disabled": "🔓 <b>2FA:</b> <code>معطل (بدون كلمة مرور)</code>",
        "order_expired_msg": "{time_e} <b>انتهت مهلة الطلب!</b>\nانتهى وقت 10 دقائق للرقم <code>{phone}</code>. تم إرجاع <b>{price} Pts</b> تلقائياً.",
        "session_logged_out_alert": "⚠️ تم تسجيل الخروج أو انتهت الجلسة بالفعل.",
        "fetching_otp_toast": "🔄 جاري جلب أحدث رمز...",
        "no_new_otp_alert": "⏳ لم يصل رمز جديد بعد. حاول مجدداً بعد ثوانٍ.",
        "otp_err_alert": "❌ خطأ أثناء جلب الرمز.",
        "session_finished_msg": "{yes} <b>تم إنهاء الجلسة وتسجيل الخروج بنجاح.</b>",
        "no_active_order_alert": "⚠️ لا يوجد طلب نشط.",
        "bulk_prompt_msg": "{store} <b>شراء جلسات {country} ({year})</b>\n\n{pts} <b>سعر الجلسة:</b> <b>{price} Pts</b>\n{pkg} <b>المتوفر:</b> {stock}\n\n👇 <b>رد على هذه الرسالة</b> بـ <b>عدد الجلسات</b> المطلوبة.",
        "not_enough_stock_msg": "{warn} <b>المخزون غير كافٍ!</b> الحد الأقصى {stock}.",
        "enter_valid_num_msg": "{no} يرجى إدخال رقم صحيح.",
        "processing_sessions_msg": "{wait} <b>جاري تجهيز الجلسات...</b>",
        "stock_changed_msg": "{no} تغير المخزون أثناء المعالجة. تم إلغاء الشراء.",
        "bulk_success_caption": "{yes} <b>تم الشراء بالجملة بنجاح!</b>\n\n{flag} الدولة: {country}\n{pkg} الكمية: {qty}\n{pts} الإجمالي المدفوع: <b>{cost} Pts</b>\n\n<i>(تم تسليم الجلسات بأمان ولا يبقيها البوت نشطة)</i>",
        "zip_err_msg": "{warn} خطأ في إنشاء ZIP: {err}",
        "support_msg": "{on} <b>دعم ومعلومات Fresh Tg</b>\n\n{warn} للدعم تواصل مع الإدارة..",
        "btn_support_url": "📩 الدعم",
        "btn_terms_url": "📜 الشروط والأحكام",
        "btn_channel_url": "📢 القناة",
        "dep_group_unavail": "{warn} <b>مجموعة الإيداع غير متاحة</b>\nيرجى التواصل مع الدعم.",
        "dep_menu_msg": "{money} <b>بوابة إيداع USDT (نقاط تلقائية)</b>\n━━━━━━━━━━━━━━━━━━━━━━\n{pts} <b>السعر:</b> <code>$1 USDT = {rate} Points</code>\n{asst} <b>بوت التحويل:</b> <code>@{tip_bot}</code>\n{acc} <b>المستلم:</b> <code>@{receiver}</code>\n\n<b>طريقة الإيداع:</b>\n1. انضم إلى مجموعة الإيداع من الزر أدناه.\n2. أرسل الأمر (مباشرة أو بالرد على المستلم):\n   <code>cc (amount) usdt @{receiver}</code>\n3. بعد تأكيد <code>@{tip_bot}</code> ستُضاف النقاط تلقائياً وسيتم إخراجك من المجموعة خلال 5 ثوانٍ.\n\n{warn} <b>تنبيه مهم:</b>\n• الإيداعات الأقل من <b>0.5 USDT</b> <b>لا تُحتسب</b>. تواصل مع الدعم إذا أرسلت أقل من 0.5 USDT.\n• عدم إرسال رسالة خلال <b>دقيقتين</b> من الدخول يؤدي إلى إخراجك تلقائياً.",
        "grp_welcome_msg": "{spark} <b>تعليمات الإيداع</b> — {mention}\n━━━━━━━━━━━━━━━━━━━━━━\n{money} أرسل التحويل (مباشرة أو بالرد على المستلم):\n<code>cc (deposit amount) usdt @{receiver}</code>\n<i>مثال:</i> <code>cc 5 usdt @{receiver}</code>\n\n{pts} <b>السعر:</b> <code>$1 USDT = {rate} Points</code>\n\n{warn} <b>قواعد مهمة:</b>\n• الإيداعات الأقل من <b>0.5 USDT</b> <b>لا تُحتسب</b>. تواصل مع الدعم إذا أرسلت أقل من 0.5 USDT.\n• أرسل رسالة خلال <b>دقيقتين</b> وإلا سيتم إخراجك تلقائياً.",
        "grp_inactive_kick": "{time_e} تم إخراج <a href='tg://user?id={uid}'>العضو</a> بعد دقيقتين من عدم النشاط.",
        "grp_wrong_token": "{warn} <a href='tg://user?id={uid}'>العضو</a>، تم رصد عملة غير مدعومة.\nيتم احتساب إيداعات <b>USDT</b> فقط تلقائياً—يرجى التواصل مع <b>الدعم</b>.",
        "grp_wrong_token_anon": "{warn} تم رصد عملة غير مدعومة. يتم احتساب <b>USDT</b> فقط—يرجى التواصل مع <b>الدعم</b>.",
        "grp_min_warn": "{warn} <a href='tg://user?id={uid}'>العضو</a>، إيداعك <b>{amt} USDT</b> أقل من الحد الأدنى <b>0.5 USDT</b>.\nالإيداعات الأقل من <b>0.5 USDT</b> لا تُحتسب—يرجى التواصل مع <b>الدعم</b>.",
        "grp_confirmed": "{yes} <a href='tg://user?id={uid}'>تم تأكيد الإيداع</a> — تمت إضافة <b>+{pts} Points</b> (${amt:.2f} USDT).\n<i>سيتم إخراجك من المجموعة خلال 5 ثوانٍ...</i>",
        "dm_deposit_credited": "{yes} تم تأكيد الإيداع — أُضيفت <b>{pts} Points</b> (${amt:.2f} USDT) إلى حسابك.\n{pts} الرصيد الجديد: <b>{bal} Points</b> | السعر: $1 = {rate} Points.",
    },
    "pt": {
        "choose_lang_title": "🌐 <b>Escolha seu idioma</b>",
        "choose_lang_desc": "Selecione o idioma que deseja usar no bot.",
        "lang_updated": "✅ Idioma alterado para <b>Português</b>!",
        "lang_set_continue": "✅ Idioma definido para <b>Português</b>!",
        "btn_language": "Idioma",
        "btn_buy_account": "Comprar Conta",
        "btn_my_profile": "Meu Perfil",
        "btn_buy_sessions": "Comprar Sessões",
        "btn_deposit": "Depositar",
        "btn_my_stats": "Minhas Estatísticas",
        "btn_support": "Suporte",
        "btn_admin_panel": "Painel Admin",
        "btn_choose_lang": "🌐 Idioma / Language",
        "btn_join_ch": "📢 Entrar no Canal ({title})",
        "btn_verify_join": "✅ Verificar Entrada",
        "btn_read_terms": "📜 Ler Termos e Condições",
        "btn_accept": "✅ Aceitar",
        "btn_reject": "❌ Rejeitar",
        "btn_cancel": "❌ Cancelar",
        "btn_back": "🔙 Voltar",
        "btn_prev": "⬅️ Ant.",
        "btn_next": "➡️ Próx.",
        "btn_buy_now": "✅ Sim, comprar agora",
        "btn_get_otp_again": "🔄 Obter OTP novamente",
        "btn_logout": "🚪 Finalizar e sair",
        "btn_purchase_logs": "📜 Histórico de compras",
        "btn_referral_logs": "👥 Indicações",
        "btn_join_dep_grp": "🏦 Grupo de Depósito",
        "btn_contact_support": "📩 Contatar Suporte",
        "bot_maintenance": "{off} <b>O bot está em manutenção.</b> Tente novamente mais tarde.",
        "bot_maintenance_alert": "⚙️ Bot em manutenção.",
        "slow_down": "⚠️ Vá com calma! Não faça spam nos botões.",
        "banned_alert": "🚫 BANIDO",
        "force_join_msg": "{warn} <b>Você precisa entrar nos nossos canais primeiro!</b>",
        "must_join_alert": "⚠️ Entre nos canais primeiro!",
        "terms_msg": "{doc} <b>TERMOS E CONDIÇÕES</b>\nLeia e aceite os Termos e Condições antes de usar o bot.",
        "terms_accepted_alert": "✅ Termos aceitos!",
        "terms_rejected_msg": "{no} Você não pode usar o bot sem aceitar os termos.",
        "cancelled_msg": "{no} <b>Cancelado.</b>",
        "welcome_msg": "👋 <b>Bem-vindo à Fresh Tg Store!</b>\n\n{pts} <b>Cotação:</b> <code>$1 USDT = {rate} Points</code>\n{gift} <b>Indique e ganhe:</b>\nConvide amigos e ganhe {pct}% dos depósitos deles em Points!\n{globe} <code>https://t.me/{bot_user}?start=ref_{ref_uid}</code>",
        "init_error": "⚠️ Erro: digite /start para inicializar sua conta.",
        "profile_msg": "{acc} <b>PERFIL DO USUÁRIO</b>\n\n{id_e} ID do usuário: <code>{uid}</code>\n{pts} Saldo: <code>{bal} Pts (${usd_bal:.2f})</code>\n{card} Depositado: <code>{dep} Pts (${usd_dep:.2f})</code>{disc_msg}\n{cal} Entrada: {joined}\n\n{users} <b>Seu link de indicação:</b>\n<code>{ref_link}</code>\n\n<i>(Compartilhe com amigos para ganhar Points!)</i>",
        "active_discount": "\n{gift} Desconto ativo: <b>{discount}% OFF</b>",
        "stats_msg": "{stats} <b>Minhas Estatísticas</b>\n\n{cart} <b>Contas compradas:</b> {orders}\n{pts} <b>Total gasto:</b> {spent} Pts (${usd_spent:.2f})\n{card} <b>Total depositado:</b> {dep} Pts (${usd_dep:.2f})",
        "ref_count_alert": "👥 Você indicou {count} usuário(s).",
        "purchase_hist_title": "{doc} <b>Histórico de compras (Pág. {page})</b>\n\n",
        "no_purchases": "Nenhuma compra encontrada.",
        "stock_empty": "{no} <b>Estoque vazio no momento. Volte mais tarde!</b>",
        "bulk_menu": "{store} <b>Menu de Sessões em Lote</b>",
        "single_menu": "{cart} <b>Menu de Conta Única</b>",
        "select_region": "{title}\n\n{globe} <b>Selecione uma região para ver números disponíveis (Pág. {page}).</b>\n{usdt} Cotação: $1 USDT = <b>{rate} Points</b>\n\n",
        "out_of_stock_alert": "❌ Sem estoque para este país.",
        "out_of_stock_short": "❌ Sem estoque!",
        "select_year_msg": "{cal} <b>Selecione o ano da conta</b>\n{globe} País: <b>{country}</b>\n\n",
        "confirm_buy_msg": "{cart} <b>Confirme sua compra</b>\n\n{flag} <b>País:</b> {country}\n{cal} <b>Ano:</b> {year}\n{pts} <b>Preço final:</b> <b>{price} Pts</b> (${usd_price:.2f})\n\n{card} <b>Seu saldo:</b> <b>{bal} Pts</b>\n\n❓ Deseja prosseguir com a compra?",
        "sold_out_alert": "❌ Esgotado! Outro usuário acabou de comprar esta conta.",
        "insufficient_bal_alert": "❌ Saldo insuficiente! Necessário {price} Pts",
        "insufficient_bal_msg": "{no} <b>Saldo insuficiente!</b>\nVocê precisa de <b>{cost} Pts</b> para {qty} sessões.",
        "fetching_num": "🔄 <b>Buscando número (+{phone})...</b>",
        "acc_invalid": "{no} <b>Conta inválida.</b> Points reembolsados. Tente outra.",
        "order_active_msg": "{yes} <b>Pedido ativo!</b>\n\n{phone_e} <b>Telefone:</b> <code>{phone}</code>\n{flag} <b>País:</b> {c_icon} {country}\n\n🔻 <b>INSTRUÇÕES:</b>\n1. Abra o Telegram e Adicionar conta\n2. Digite o número acima.\n3. {wait} <b>Aguarde!</b> O bot aguarda seu OTP e enviará automaticamente.\n\n<i>Se não chegar OTP em 10 minutos, o pedido será cancelado e reembolsado.</i>",
        "otp_fetched_msg": "{yes} <b>Último OTP obtido!</b>\n\n{phone_e} <b>Telefone:</b> <code>{phone}</code>\n{flag} <b>País:</b> {c_icon} {country}\n{otp_e} <b>OTP:</b> <code>{code}</code>\n{twofa_line}",
        "twofa_enabled": "{twofa} <b>2FA:</b> <code>{pwd}</code>",
        "twofa_disabled": "🔓 <b>2FA:</b> <code>Desativada (Sem senha)</code>",
        "order_expired_msg": "{time_e} <b>Pedido expirado!</b>\nLimite de 10 minutos encerrado para <code>{phone}</code>. Seus <b>{price} Pts</b> foram reembolsados.",
        "session_logged_out_alert": "⚠️ Sessão já encerrada ou expirada.",
        "fetching_otp_toast": "🔄 Buscando OTP mais recente...",
        "no_new_otp_alert": "⏳ Nenhum OTP novo ainda. Tente novamente em instantes.",
        "otp_err_alert": "❌ Erro ao obter OTP.",
        "session_finished_msg": "{yes} <b>Sessão finalizada e desconectada.</b>",
        "no_active_order_alert": "⚠️ Nenhum pedido ativo.",
        "bulk_prompt_msg": "{store} <b>Comprar sessões {country} ({year})</b>\n\n{pts} <b>Preço por sessão:</b> <b>{price} Pts</b>\n{pkg} <b>Estoque disponível:</b> {stock}\n\n👇 <b>Responda a esta mensagem</b> com a <b>quantidade de sessões</b> desejada.",
        "not_enough_stock_msg": "{warn} <b>Estoque insuficiente!</b> Máximo: {stock}.",
        "enter_valid_num_msg": "{no} Digite um número válido.",
        "processing_sessions_msg": "{wait} <b>Processando suas sessões...</b>",
        "stock_changed_msg": "{no} O estoque mudou durante o processo. Compra cancelada.",
        "bulk_success_caption": "{yes} <b>Compra em lote concluída!</b>\n\n{flag} País: {country}\n{pkg} Quantidade: {qty}\n{pts} Total pago: <b>{cost} Pts</b>\n\n<i>(Sessões entregues com segurança, o bot não as mantém ativas)</i>",
        "zip_err_msg": "{warn} Erro ao criar ZIP: {err}",
        "support_msg": "{on} <b>Suporte e informações Fresh Tg</b>\n\n{warn} Para suporte contate o administrador..",
        "btn_support_url": "📩 Suporte",
        "btn_terms_url": "📜 Termos e Condições",
        "btn_channel_url": "📢 Canal",
        "dep_group_unavail": "{warn} <b>Grupo de depósito indisponível</b>\nContate o Suporte.",
        "dep_menu_msg": "{money} <b>PORTAL DE DEPÓSITO USDT (AUTO POINTS)</b>\n━━━━━━━━━━━━━━━━━━━━━━\n{pts} <b>Cotação:</b> <code>$1 USDT = {rate} Points</code>\n{asst} <b>Processador:</b> <code>@{tip_bot}</code>\n{acc} <b>Destinatário:</b> <code>@{receiver}</code>\n\n<b>Como depositar:</b>\n1. Entre no Grupo de Depósito pelo botão abaixo.\n2. Envie sua gorjeta (direto ou respondendo ao destinatário):\n   <code>cc (amount) usdt @{receiver}</code>\n3. Quando <code>@{tip_bot}</code> confirmar, os Points são creditados e você é removido do grupo em 5 segundos.\n\n{warn} <b>Aviso importante:</b>\n• Depósitos abaixo de <b>0.5 USDT</b> <b>não</b> serão contabilizados. Contate o Suporte se enviou menos de 0.5 USDT.\n• Sem enviar mensagem em <b>2 minutos</b> após entrar, você será removido automaticamente.",
        "grp_welcome_msg": "{spark} <b>INSTRUÇÕES DE DEPÓSITO</b> — {mention}\n━━━━━━━━━━━━━━━━━━━━━━\n{money} Envie sua gorjeta (direto ou respondendo ao destinatário):\n<code>cc (deposit amount) usdt @{receiver}</code>\n<i>Exemplo:</i> <code>cc 5 usdt @{receiver}</code>\n\n{pts} <b>Cotação:</b> <code>$1 USDT = {rate} Points</code>\n\n{warn} <b>Regras importantes:</b>\n• Depósitos abaixo de <b>0.5 USDT</b> <b>não</b> serão contabilizados. Contate o Suporte se enviou menos de 0.5 USDT.\n• Envie uma mensagem em até <b>2 minutos</b> ou você será removido.",
        "grp_inactive_kick": "{time_e} <a href='tg://user?id={uid}'>Membro</a> removido após 2 minutos de inatividade.",
        "grp_wrong_token": "{warn} <a href='tg://user?id={uid}'>Membro</a>, moeda não suportada detectada.\nApenas depósitos em <b>USDT</b> são creditados automaticamente—contate o <b>Suporte</b>.",
        "grp_wrong_token_anon": "{warn} Moeda não suportada detectada. Apenas <b>USDT</b> é aceito—contate o <b>Suporte</b>.",
        "grp_min_warn": "{warn} <a href='tg://user?id={uid}'>Membro</a>, seu depósito de <b>{amt} USDT</b> está abaixo do mínimo de <b>0.5 USDT</b>.\nDepósitos abaixo de <b>0.5 USDT</b> não são contabilizados—contate o <b>Suporte</b>.",
        "grp_confirmed": "{yes} <a href='tg://user?id={uid}'>Depósito confirmado</a> — <b>+{pts} Points</b> (${amt:.2f} USDT) creditados.\n<i>Removendo do grupo em 5 segundos...</i>",
        "dm_deposit_credited": "{yes} Depósito creditado — <b>{pts} Points</b> (${amt:.2f} USDT) adicionados à sua conta.\n{pts} Novo saldo: <b>{bal} Points</b> | Cotação: $1 = {rate} Points.",
    },
    "id": {
        "choose_lang_title": "🌐 <b>Pilih Bahasa Anda</b>",
        "choose_lang_desc": "Pilih bahasa yang ingin Anda gunakan di bot.",
        "lang_updated": "✅ Bahasa diubah ke <b>Bahasa Indonesia</b>!",
        "lang_set_continue": "✅ Bahasa diatur ke <b>Bahasa Indonesia</b>!",
        "btn_language": "Bahasa",
        "btn_buy_account": "Beli Akun",
        "btn_my_profile": "Profil Saya",
        "btn_buy_sessions": "Beli Sesi",
        "btn_deposit": "Deposit",
        "btn_my_stats": "Statistik Saya",
        "btn_support": "Dukungan",
        "btn_admin_panel": "Panel Admin",
        "btn_choose_lang": "🌐 Bahasa / Language",
        "btn_join_ch": "📢 Gabung Channel ({title})",
        "btn_verify_join": "✅ Verifikasi Gabung",
        "btn_read_terms": "📜 Baca Syarat & Ketentuan",
        "btn_accept": "✅ Setuju",
        "btn_reject": "❌ Tolak",
        "btn_cancel": "❌ Batal",
        "btn_back": "🔙 Kembali",
        "btn_prev": "⬅️ Seb.",
        "btn_next": "➡️ Ber.",
        "btn_buy_now": "✅ Ya, Beli Sekarang",
        "btn_get_otp_again": "🔄 Ambil OTP Lagi",
        "btn_logout": "🚪 Selesai & Keluar",
        "btn_purchase_logs": "📜 Riwayat Pembelian",
        "btn_referral_logs": "👥 Referral",
        "btn_join_dep_grp": "🏦 Gabung Grup Deposit",
        "btn_contact_support": "📩 Hubungi Dukungan",
        "bot_maintenance": "{off} <b>Bot sedang dalam pemeliharaan.</b> Silakan coba lagi nanti.",
        "bot_maintenance_alert": "⚙️ Bot sedang dalam pemeliharaan.",
        "slow_down": "⚠️ Harap pelan-pelan! Jangan spam tombol.",
        "banned_alert": "🚫 DIBLOKIR",
        "force_join_msg": "{warn} <b>Anda harus bergabung ke channel kami terlebih dahulu!</b>",
        "must_join_alert": "⚠️ Anda harus bergabung ke channel dulu!",
        "terms_msg": "{doc} <b>SYARAT & KETENTUAN</b>\nHarap baca dan setujui Syarat & Ketentuan sebelum menggunakan bot.",
        "terms_accepted_alert": "✅ Syarat disetujui!",
        "terms_rejected_msg": "{no} Anda tidak dapat menggunakan bot tanpa menyetujui syarat.",
        "cancelled_msg": "{no} <b>Dibatalkan.</b>",
        "welcome_msg": "👋 <b>Selamat datang di Fresh Tg Store!</b>\n\n{pts} <b>Kurs:</b> <code>$1 USDT = {rate} Points</code>\n{gift} <b>Ajak & Dapatkan:</b>\nUndang teman dan dapatkan {pct}% dari deposit mereka dalam Points!\n{globe} <code>https://t.me/{bot_user}?start=ref_{ref_uid}</code>",
        "init_error": "⚠️ Error: ketik /start untuk menginisialisasi akun Anda.",
        "profile_msg": "{acc} <b>PROFIL PENGGUNA</b>\n\n{id_e} ID Pengguna: <code>{uid}</code>\n{pts} Saldo: <code>{bal} Pts (${usd_bal:.2f})</code>\n{card} Total Deposit: <code>{dep} Pts (${usd_dep:.2f})</code>{disc_msg}\n{cal} Bergabung: {joined}\n\n{users} <b>Link Referral Anda:</b>\n<code>{ref_link}</code>\n\n<i>(Bagikan link ini ke teman untuk mendapatkan bonus Points!)</i>",
        "active_discount": "\n{gift} Diskon Aktif: <b>{discount}% OFF</b>",
        "stats_msg": "{stats} <b>Statistik Saya</b>\n\n{cart} <b>Akun Dibeli:</b> {orders}\n{pts} <b>Total Pengeluaran:</b> {spent} Pts (${usd_spent:.2f})\n{card} <b>Total Deposit:</b> {dep} Pts (${usd_dep:.2f})",
        "ref_count_alert": "👥 Anda telah mereferensikan {count} pengguna.",
        "purchase_hist_title": "{doc} <b>Riwayat Pembelian (Hal. {page})</b>\n\n",
        "no_purchases": "Belum ada pembelian.",
        "stock_empty": "{no} <b>Stok sedang kosong. Cek kembali nanti!</b>",
        "bulk_menu": "{store} <b>Menu Sesi Massal</b>",
        "single_menu": "{cart} <b>Menu Akun Satuan</b>",
        "select_region": "{title}\n\n{globe} <b>Pilih wilayah untuk melihat nomor tersedia (Hal. {page}).</b>\n{usdt} Kurs: $1 USDT = <b>{rate} Points</b>\n\n",
        "out_of_stock_alert": "❌ Stok habis untuk negara ini.",
        "out_of_stock_short": "❌ Stok habis!",
        "select_year_msg": "{cal} <b>Pilih Tahun Akun</b>\n{globe} Negara: <b>{country}</b>\n\n",
        "confirm_buy_msg": "{cart} <b>Konfirmasi Pembelian Anda</b>\n\n{flag} <b>Negara:</b> {country}\n{cal} <b>Tahun:</b> {year}\n{pts} <b>Harga Akhir:</b> <b>{price} Pts</b> (${usd_price:.2f})\n\n{card} <b>Saldo Anda:</b> <b>{bal} Pts</b>\n\n❓ Apakah Anda ingin melanjutkan pembelian ini?",
        "sold_out_alert": "❌ Habis terjual! Pengguna lain baru saja membeli akun ini.",
        "insufficient_bal_alert": "❌ Saldo tidak cukup! Butuh {price} Pts",
        "insufficient_bal_msg": "{no} <b>Saldo tidak cukup!</b>\nAnda butuh <b>{cost} Pts</b> untuk membeli {qty} sesi.",
        "fetching_num": "🔄 <b>Mengambil nomor (+{phone})...</b>",
        "acc_invalid": "{no} <b>Akun tidak valid.</b> Points dikembalikan. Coba akun lain.",
        "order_active_msg": "{yes} <b>Pesanan Aktif!</b>\n\n{phone_e} <b>Telepon:</b> <code>{phone}</code>\n{flag} <b>Negara:</b> {c_icon} {country}\n\n🔻 <b>INSTRUKSI:</b>\n1. Buka Telegram & Tambah Akun\n2. Masukkan nomor di atas.\n3. {wait} <b>Harap tunggu!</b> Bot memantau OTP dan akan mengirimkannya otomatis.\n\n<i>Catatan: jika OTP tidak masuk dalam 10 menit, pesanan dibatalkan dan Points dikembalikan otomatis.</i>",
        "otp_fetched_msg": "{yes} <b>OTP Terbaru Diterima!</b>\n\n{phone_e} <b>Telepon:</b> <code>{phone}</code>\n{flag} <b>Negara:</b> {c_icon} {country}\n{otp_e} <b>OTP:</b> <code>{code}</code>\n{twofa_line}",
        "twofa_enabled": "{twofa} <b>2FA:</b> <code>{pwd}</code>",
        "twofa_disabled": "🔓 <b>2FA:</b> <code>Nonaktif (Tanpa Password)</code>",
        "order_expired_msg": "{time_e} <b>Pesanan Kedaluwarsa!</b>\nBatas 10 menit untuk <code>{phone}</code> telah habis. <b>{price} Pts</b> Anda telah dikembalikan.",
        "session_logged_out_alert": "⚠️ Sesi sudah keluar atau kedaluwarsa.",
        "fetching_otp_toast": "🔄 Mengambil OTP terbaru...",
        "no_new_otp_alert": "⏳ Belum ada OTP baru. Coba lagi beberapa detik.",
        "otp_err_alert": "❌ Gagal mengambil OTP.",
        "session_finished_msg": "{yes} <b>Sesi selesai dan berhasil keluar.</b>",
        "no_active_order_alert": "⚠️ Tidak ada pesanan aktif.",
        "bulk_prompt_msg": "{store} <b>Beli Sesi {country} ({year})</b>\n\n{pts} <b>Harga per sesi:</b> <b>{price} Pts</b>\n{pkg} <b>Stok Tersedia:</b> {stock}\n\n👇 <b>Balas pesan ini</b> dengan <b>jumlah sesi</b> yang ingin dibeli.",
        "not_enough_stock_msg": "{warn} <b>Stok tidak mencukupi!</b> Maksimal {stock}.",
        "enter_valid_num_msg": "{no} Masukkan angka yang valid.",
        "processing_sessions_msg": "{wait} <b>Memproses sesi Anda...</b>",
        "stock_changed_msg": "{no} Stok berubah saat diproses. Pembelian dibatalkan.",
        "bulk_success_caption": "{yes} <b>Pembelian Massal Berhasil!</b>\n\n{flag} Negara: {country}\n{pkg} Jumlah: {qty}\n{pts} Total Dibayar: <b>{cost} Pts</b>\n\n<i>(Sesi diberikan dengan aman, bot tidak menyimpannya tetap aktif)</i>",
        "zip_err_msg": "{warn} Gagal membuat ZIP: {err}",
        "support_msg": "{on} <b>Dukungan & Informasi Fresh Tg</b>\n\n{warn} Untuk bantuan hubungi Admin..",
        "btn_support_url": "📩 Dukungan",
        "btn_terms_url": "📜 Syarat & Ketentuan",
        "btn_channel_url": "📢 Channel",
        "dep_group_unavail": "{warn} <b>Grup Deposit belum diatur</b>\nHubungi Dukungan.",
        "dep_menu_msg": "{money} <b>PORTAL DEPOSIT USDT (AUTO POINTS)</b>\n━━━━━━━━━━━━━━━━━━━━━━\n{pts} <b>Kurs:</b> <code>$1 USDT = {rate} Points</code>\n{asst} <b>Pemroses Tip:</b> <code>@{tip_bot}</code>\n{acc} <b>Penerima:</b> <code>@{receiver}</code>\n\n<b>Cara Deposit:</b>\n1. Gabung ke Grup Deposit melalui tombol di bawah.\n2. Kirim tip Anda (langsung atau membalas penerima):\n   <code>cc (amount) usdt @{receiver}</code>\n3. Setelah <code>@{tip_bot}</code> mengonfirmasi, Points otomatis masuk dan Anda dikeluarkan dari grup dalam 5 detik.\n\n{warn} <b>Peringatan Penting:</b>\n• Deposit di bawah <b>0.5 USDT</b> <b>tidak</b> dihitung. Hubungi Dukungan jika Anda mengirim kurang dari 0.5 USDT.\n• Jika tidak mengirim pesan dalam <b>2 menit</b> setelah masuk, Anda akan dikeluarkan otomatis.",
        "grp_welcome_msg": "{spark} <b>INSTRUKSI DEPOSIT</b> — {mention}\n━━━━━━━━━━━━━━━━━━━━━━\n{money} Kirim tip Anda (langsung atau membalas penerima):\n<code>cc (deposit amount) usdt @{receiver}</code>\n<i>Contoh:</i> <code>cc 5 usdt @{receiver}</code>\n\n{pts} <b>Kurs:</b> <code>$1 USDT = {rate} Points</code>\n\n{warn} <b>Aturan Penting:</b>\n• Deposit di bawah <b>0.5 USDT</b> <b>tidak</b> dihitung. Hubungi Dukungan jika Anda mengirim kurang dari 0.5 USDT.\n• Kirim pesan dalam <b>2 menit</b> atau Anda akan dikeluarkan otomatis.",
        "grp_inactive_kick": "{time_e} <a href='tg://user?id={uid}'>Anggota</a> dikeluarkan karena tidak aktif selama 2 menit.",
        "grp_wrong_token": "{warn} <a href='tg://user?id={uid}'>Anggota</a>, token tidak didukung terdeteksi.\nHanya deposit <b>USDT</b> yang diproses otomatis—hubungi <b>Dukungan</b>.",
        "grp_wrong_token_anon": "{warn} Token tidak didukung terdeteksi. Hanya <b>USDT</b> yang diproses—hubungi <b>Dukungan</b>.",
        "grp_min_warn": "{warn} <a href='tg://user?id={uid}'>Anggota</a>, deposit Anda <b>{amt} USDT</b> di bawah minimum <b>0.5 USDT</b>.\nDeposit di bawah <b>0.5 USDT</b> tidak dihitung—hubungi <b>Dukungan</b>.",
        "grp_confirmed": "{yes} <a href='tg://user?id={uid}'>Deposit Terkonfirmasi</a> — <b>+{pts} Points</b> (${amt:.2f} USDT) ditambahkan.\n<i>Mengeluarkan dari grup dalam 5 detik...</i>",
        "dm_deposit_credited": "{yes} Deposit Berhasil — <b>{pts} Points</b> (${amt:.2f} USDT) ditambahkan ke akun Anda.\n{pts} Saldo Baru: <b>{bal} Points</b> | Kurs: $1 = {rate} Points.",
    },
    "zh": {
        "choose_lang_title": "🌐 <b>选择您的语言</b>",
        "choose_lang_desc": "选择您要在机器人中使用的语言。",
        "lang_updated": "✅ 语言已切换为 <b>中文</b>！",
        "lang_set_continue": "✅ 语言已设置为 <b>中文</b>！",
        "btn_language": "语言",
        "btn_buy_account": "购买账号",
        "btn_my_profile": "个人资料",
        "btn_buy_sessions": "购买 Sessions",
        "btn_deposit": "充值",
        "btn_my_stats": "我的统计",
        "btn_support": "客服支持",
        "btn_admin_panel": "管理面板",
        "btn_choose_lang": "🌐 语言 / Language",
        "btn_join_ch": "📢 加入频道 ({title})",
        "btn_verify_join": "✅ 验证已加入",
        "btn_read_terms": "📜 阅读条款与细则",
        "btn_accept": "✅ 同意",
        "btn_reject": "❌ 拒绝",
        "btn_cancel": "❌ 取消",
        "btn_back": "🔙 返回",
        "btn_prev": "⬅️ 上一页",
        "btn_next": "➡️ 下一页",
        "btn_buy_now": "✅ 确认购买",
        "btn_get_otp_again": "🔄 重新获取验证码",
        "btn_logout": "🚪 完成并退出",
        "btn_purchase_logs": "📜 购买记录",
        "btn_referral_logs": "👥 推广记录",
        "btn_join_dep_grp": "🏦 加入充值群",
        "btn_contact_support": "📩 联系客服",
        "bot_maintenance": "{off} <b>机器人正在维护中。</b>请稍后再试。",
        "bot_maintenance_alert": "⚙️ 机器人维护中。",
        "slow_down": "⚠️ 请勿频繁点击按钮！",
        "banned_alert": "🚫 已封禁",
        "force_join_msg": "{warn} <b>请先加入我们的频道！</b>",
        "must_join_alert": "⚠️ 请先加入频道！",
        "terms_msg": "{doc} <b>服务条款</b>\n使用机器人前请阅读并同意服务条款。",
        "terms_accepted_alert": "✅ 已同意条款！",
        "terms_rejected_msg": "{no} 不同意条款将无法使用机器人。",
        "cancelled_msg": "{no} <b>已取消。</b>",
        "welcome_msg": "👋 <b>欢迎来到 Fresh Tg Store！</b>\n\n{pts} <b>汇率：</b> <code>$1 USDT = {rate} Points</code>\n{gift} <b>邀请奖励：</b>\n邀请好友可获得其充值 {pct}% 的 Points 奖励！\n{globe} <code>https://t.me/{bot_user}?start=ref_{ref_uid}</code>",
        "init_error": "⚠️ 错误：请发送 /start 初始化您的账号。",
        "profile_msg": "{acc} <b>用户资料</b>\n\n{id_e} 用户 ID：<code>{uid}</code>\n{pts} 余额：<code>{bal} Pts (${usd_bal:.2f})</code>\n{card} 累计充值：<code>{dep} Pts (${usd_dep:.2f})</code>{disc_msg}\n{cal} 加入时间：{joined}\n\n{users} <b>您的邀请链接：</b>\n<code>{ref_link}</code>\n\n<i>（分享链接给好友即可赚取 Points 奖励！）</i>",
        "active_discount": "\n{gift} 当前折扣：<b>{discount}% OFF</b>",
        "stats_msg": "{stats} <b>我的统计</b>\n\n{cart} <b>已购账号：</b>{orders}\n{pts} <b>累计消费：</b>{spent} Pts (${usd_spent:.2f})\n{card} <b>累计充值：</b>{dep} Pts (${usd_dep:.2f})",
        "ref_count_alert": "👥 您已邀请 {count} 位用户。",
        "purchase_hist_title": "{doc} <b>购买记录（第 {page} 页）</b>\n\n",
        "no_purchases": "暂无购买记录。",
        "stock_empty": "{no} <b>当前暂无库存，请稍后再试！</b>",
        "bulk_menu": "{store} <b>批量 Session 菜单</b>",
        "single_menu": "{cart} <b>单号购买菜单</b>",
        "select_region": "{title}\n\n{globe} <b>请选择地区查看可用号码（第 {page} 页）。</b>\n{usdt} 汇率：$1 USDT = <b>{rate} Points</b>\n\n",
        "out_of_stock_alert": "❌ 该地区暂无库存。",
        "out_of_stock_short": "❌ 已售罄！",
        "select_year_msg": "{cal} <b>选择账号年份</b>\n{globe} 地区：<b>{country}</b>\n\n",
        "confirm_buy_msg": "{cart} <b>确认购买</b>\n\n{flag} <b>地区：</b>{country}\n{cal} <b>年份：</b>{year}\n{pts} <b>应付金额：</b><b>{price} Pts</b> (${usd_price:.2f})\n\n{card} <b>当前余额：</b><b>{bal} Pts</b>\n\n❓ 是否确认购买？",
        "sold_out_alert": "❌ 已售罄！其他用户刚刚购买了此账号。",
        "insufficient_bal_alert": "❌ 余额不足！需要 {price} Pts",
        "insufficient_bal_msg": "{no} <b>余额不足！</b>\n购买 {qty} 个 Session 需要 <b>{cost} Pts</b>。",
        "fetching_num": "🔄 <b>正在获取号码 (+{phone})...</b>",
        "acc_invalid": "{no} <b>账号无效。</b>Points 已退回，请尝试其他账号。",
        "order_active_msg": "{yes} <b>订单已激活！</b>\n\n{phone_e} <b>号码：</b><code>{phone}</code>\n{flag} <b>地区：</b>{c_icon} {country}\n\n🔻 <b>操作说明：</b>\n1. 打开 Telegram 并选择添加账号\n2. 输入上方号码。\n3. {wait} <b>请稍候！</b>机器人正在监听验证码并自动发送。\n\n<i>注意：若 10 分钟内未收到验证码，订单将自动取消并退还 Points。</i>",
        "otp_fetched_msg": "{yes} <b>已获取最新验证码！</b>\n\n{phone_e} <b>号码：</b><code>{phone}</code>\n{flag} <b>地区：</b>{c_icon} {country}\n{otp_e} <b>验证码：</b><code>{code}</code>\n{twofa_line}",
        "twofa_enabled": "{twofa} <b>两步验证：</b><code>{pwd}</code>",
        "twofa_disabled": "🔓 <b>两步验证：</b><code>未开启（无密码）</code>",
        "order_expired_msg": "{time_e} <b>订单已超时！</b>\n<code>{phone}</code> 的 10 分钟等待时间已结束，<b>{price} Pts</b> 已自动退回。",
        "session_logged_out_alert": "⚠️ 会话已退出或已过期。",
        "fetching_otp_toast": "🔄 正在获取最新验证码...",
        "no_new_otp_alert": "⏳ 暂未收到新验证码，请稍后再试。",
        "otp_err_alert": "❌ 获取验证码失败。",
        "session_finished_msg": "{yes} <b>会话已结束并成功退出。</b>",
        "no_active_order_alert": "⚠️ 没有进行中的订单。",
        "bulk_prompt_msg": "{store} <b>购买 {country} ({year}) Sessions</b>\n\n{pts} <b>单个价格：</b><b>{price} Pts</b>\n{pkg} <b>可用库存：</b>{stock}\n\n👇 <b>回复此消息</b>输入要购买的 <b>Session 数量</b>。",
        "not_enough_stock_msg": "{warn} <b>库存不足！</b>最多可买 {stock} 个。",
        "enter_valid_num_msg": "{no} 请输入有效数字。",
        "processing_sessions_msg": "{wait} <b>正在打包 Session...</b>",
        "stock_changed_msg": "{no} 处理期间库存发生变化，购买已取消。",
        "bulk_success_caption": "{yes} <b>批量购买成功！</b>\n\n{flag} 地区：{country}\n{pkg} 数量：{qty}\n{pts} 实付金额：<b>{cost} Pts</b>\n\n<i>（Session 已安全交付，机器人不会保持在线）</i>",
        "zip_err_msg": "{warn} 创建压缩包失败：{err}",
        "support_msg": "{on} <b>Fresh Tg 客服与相关信息</b>\n\n{warn} 如需帮助请联系管理员..",
        "btn_support_url": "📩 联系客服",
        "btn_terms_url": "📜 服务条款",
        "btn_channel_url": "📢 官方频道",
        "dep_group_unavail": "{warn} <b>充值群未配置</b>\n请联系客服。",
        "dep_menu_msg": "{money} <b>USDT 充值中心（自动到账 Points）</b>\n━━━━━━━━━━━━━━━━━━━━━━\n{pts} <b>汇率：</b><code>$1 USDT = {rate} Points</code>\n{asst} <b>打赏机器人：</b><code>@{tip_bot}</code>\n{acc} <b>收款账号：</b><code>@{receiver}</code>\n\n<b>充值步骤：</b>\n1. 点击下方按钮加入官方充值群。\n2. 在群内发送（直接发送或回复收款人）：\n   <code>cc (amount) usdt @{receiver}</code>\n3. <code>@{tip_bot}</code> 确认后自动入账 Points，5 秒后将自动移出充值群。\n\n{warn} <b>重要提示：</b>\n• 低于 <b>0.5 USDT</b> 的充值<b>不会计入</b>。若已支付少于 0.5 USDT 请联系客服。\n• 入群后 <b>2 分钟</b>内未发送消息将被自动移出。",
        "grp_welcome_msg": "{spark} <b>充值说明</b> — {mention}\n━━━━━━━━━━━━━━━━━━━━━━\n{money} 发送打赏指令（直接发送或回复收款人）：\n<code>cc (deposit amount) usdt @{receiver}</code>\n<i>示例：</i><code>cc 5 usdt @{receiver}</code>\n\n{pts} <b>汇率：</b> <code>$1 USDT = {rate} Points</code>\n\n{warn} <b>重要规则：</b>\n• 低于 <b>0.5 USDT</b> 的充值<b>不会计入</b>。若已支付少于 0.5 USDT 请联系客服。\n• 请在 <b>2 分钟</b>内发送消息，否则将被自动移出。",
        "grp_inactive_kick": "{time_e} <a href='tg://user?id={uid}'>用户</a> 因 2 分钟内无操作已被移出。",
        "grp_wrong_token": "{warn} <a href='tg://user?id={uid}'>用户</a>，检测到不支持的币种。\n仅自动入账 <b>USDT</b> 充值—请联系<b>客服</b>处理。",
        "grp_wrong_token_anon": "{warn} 检测到不支持的币种，仅自动入账 <b>USDT</b>—请联系<b>客服</b>。",
        "grp_min_warn": "{warn} <a href='tg://user?id={uid}'>用户</a>，您的充值金额 <b>{amt} USDT</b> 低于最低限额 <b>0.5 USDT</b>。\n低于 <b>0.5 USDT</b> 不会计入—若已付款请联系<b>客服</b>。",
        "grp_confirmed": "{yes} <a href='tg://user?id={uid}'>充值已确认</a> — 已到账 <b>+{pts} Points</b> (${amt:.2f} USDT)。\n<i>5 秒后将移出充值群...</i>",
        "dm_deposit_credited": "{yes} 充值已到账 — 您的账户已增加 <b>{pts} Points</b> (${amt:.2f} USDT)。\n{pts} 当前余额：<b>{bal} Points</b> | 汇率：$1 = {rate} Points。",
    },
    "fa": {
        "choose_lang_title": "🌐 <b>زبان خود را انتخاب کنید</b>",
        "choose_lang_desc": "زبانی را که می‌خواهید در ربات استفاده کنید انتخاب نمایید.",
        "lang_updated": "✅ زبان به <b>فارسی</b> تغییر یافت!",
        "lang_set_continue": "✅ زبان روی <b>فارسی</b> تنظیم شد!",
        "btn_language": "زبان",
        "btn_buy_account": "خرید اکانت",
        "btn_my_profile": "پروفایل من",
        "btn_buy_sessions": "خرید سشن",
        "btn_deposit": "واریز",
        "btn_my_stats": "آمار من",
        "btn_support": "پشتیبانی",
        "btn_admin_panel": "پنل ادمین",
        "btn_choose_lang": "🌐 زبان / Language",
        "btn_join_ch": "📢 عضویت در کانال ({title})",
        "btn_verify_join": "✅ تایید عضویت",
        "btn_read_terms": "📜 مطالعه قوانین و مقررات",
        "btn_accept": "✅ قبول دارم",
        "btn_reject": "❌ رد می‌کنم",
        "btn_cancel": "❌ لغو",
        "btn_back": "🔙 بازگشت",
        "btn_prev": "⬅️ قبلی",
        "btn_next": "➡️ بعدی",
        "btn_buy_now": "✅ بله، اکنون بخر",
        "btn_get_otp_again": "🔄 دریافت مجدد کد",
        "btn_logout": "🚪 پایان و خروج",
        "btn_purchase_logs": "📜 تاریخچه خرید",
        "btn_referral_logs": "👥 زیرمجموعه‌ها",
        "btn_join_dep_grp": "🏦 گروه واریز",
        "btn_contact_support": "📩 تماس با پشتیبانی",
        "bot_maintenance": "{off} <b>ربات در حال تعمیر و نگهداری است.</b> لطفاً بعداً تلاش کنید.",
        "bot_maintenance_alert": "⚙️ ربات در حال نگهداری است.",
        "slow_down": "⚠️ لطفاً کمی صبر کنید و دکمه‌ها را پشت سر هم نزنید.",
        "banned_alert": "🚫 مسدود شده",
        "force_join_msg": "{warn} <b>ابتدا باید در کانال‌های ما عضو شوید!</b>",
        "must_join_alert": "⚠️ ابتدا باید در کانال‌ها عضو شوید!",
        "terms_msg": "{doc} <b>قوانین و مقررات</b>\nلطفاً قبل از استفاده از ربات قوانین را مطالعه و تایید کنید.",
        "terms_accepted_alert": "✅ قوانین تایید شد!",
        "terms_rejected_msg": "{no} بدون تایید قوانین نمی‌توانید از ربات استفاده کنید.",
        "cancelled_msg": "{no} <b>لغو شد.</b>",
        "welcome_msg": "👋 <b>به Fresh Tg Store خوش آمدید!</b>\n\n{pts} <b>نرخ تبدیل:</b> <code>$1 USDT = {rate} Points</code>\n{gift} <b>دعوت و کسب درآمد:</b>\nدوستان خود را دعوت کنید و {pct}% از واریز آن‌ها را به صورت Points بگیرید!\n{globe} <code>https://t.me/{bot_user}?start=ref_{ref_uid}</code>",
        "init_error": "⚠️ خطا: برای فعال‌سازی حساب خود /start را بزنید.",
        "profile_msg": "{acc} <b>پروفایل کاربری</b>\n\n{id_e} شناسه کاربری: <code>{uid}</code>\n{pts} موجودی: <code>{bal} Pts (${usd_bal:.2f})</code>\n{card} کل واریز: <code>{dep} Pts (${usd_dep:.2f})</code>{disc_msg}\n{cal} عضویت: {joined}\n\n{users} <b>لینک دعوت شما:</b>\n<code>{ref_link}</code>\n\n<i>(لینک را با دوستان خود به اشتراک بگذارید!)</i>",
        "active_discount": "\n{gift} تخفیف فعال: <b>{discount}% OFF</b>",
        "stats_msg": "{stats} <b>آمار من</b>\n\n{cart} <b>اکانت‌های خریداری‌شده:</b> {orders}\n{pts} <b>کل هزینه:</b> {spent} Pts (${usd_spent:.2f})\n{card} <b>کل واریزی:</b> {dep} Pts (${usd_dep:.2f})",
        "ref_count_alert": "👥 شما {count} کاربر را دعوت کرده‌اید.",
        "purchase_hist_title": "{doc} <b>تاریخچه خرید (صفحه {page})</b>\n\n",
        "no_purchases": "خریدی ثبت نشده است.",
        "stock_empty": "{no} <b>در حال حاضر موجودی تمام شده است. بعداً سر بزنید!</b>",
        "bulk_menu": "{store} <b>منوی خرید عمده سشن</b>",
        "single_menu": "{cart} <b>منوی خرید تک اکانت</b>",
        "select_region": "{title}\n\n{globe} <b>برای مشاهده شماره‌های موجود کشور را انتخاب کنید (صفحه {page}).</b>\n{usdt} نرخ: $1 USDT = <b>{rate} Points</b>\n\n",
        "out_of_stock_alert": "❌ برای این کشور موجودی وجود ندارد.",
        "out_of_stock_short": "❌ ناموجود!",
        "select_year_msg": "{cal} <b>سال اکانت را انتخاب کنید</b>\n{globe} کشور: <b>{country}</b>\n\n",
        "confirm_buy_msg": "{cart} <b>تایید خرید</b>\n\n{flag} <b>کشور:</b> {country}\n{cal} <b>سال:</b> {year}\n{pts} <b>مبلغ نهایی:</b> <b>{price} Pts</b> (${usd_price:.2f})\n\n{card} <b>موجودی شما:</b> <b>{bal} Pts</b>\n\n❓ آیا می‌خواهید خرید را انجام دهید؟",
        "sold_out_alert": "❌ به اتمام رسید! کاربر دیگری این اکانت را خرید.",
        "insufficient_bal_alert": "❌ موجودی کافی نیست! {price} Pts لازم است",
        "insufficient_bal_msg": "{no} <b>موجودی کافی نیست!</b>\nبرای خرید {qty} سشن به <b>{cost} Pts</b> نیاز دارید.",
        "fetching_num": "🔄 <b>در حال دریافت شماره (+{phone})...</b>",
        "acc_invalid": "{no} <b>اکانت نامعتبر است.</b> Points بازگردانده شد. اکانت دیگری امتحان کنید.",
        "order_active_msg": "{yes} <b>سفارش فعال شد!</b>\n\n{phone_e} <b>شماره:</b> <code>{phone}</code>\n{flag} <b>کشور:</b> {c_icon} {country}\n\n🔻 <b>دستورالعمل:</b>\n1. تلگرام را باز کرده و Add Account را بزنید\n2. شماره بالا را وارد کنید.\n3. {wait} <b>منتظر بمانید!</b> ربات کد را دریافت و ارسال می‌کند.\n\n<i>اگر تا 10 دقیقه کدی نیاید، سفارش لغو و Points بازگردانده می‌شود.</i>",
        "otp_fetched_msg": "{yes} <b>آخرین کد دریافت شد!</b>\n\n{phone_e} <b>شماره:</b> <code>{phone}</code>\n{flag} <b>کشور:</b> {c_icon} {country}\n{otp_e} <b>کد:</b> <code>{code}</code>\n{twofa_line}",
        "twofa_enabled": "{twofa} <b>رمز دومرحله‌ای:</b> <code>{pwd}</code>",
        "twofa_disabled": "🔓 <b>رمز دومرحله‌ای:</b> <code>غیرفعال (بدون رمز)</code>",
        "order_expired_msg": "{time_e} <b>مهلت سفارش تمام شد!</b>\nزمان 10 دقیقه‌ای برای <code>{phone}</code> پایان یافت. <b>{price} Pts</b> بازگردانده شد.",
        "session_logged_out_alert": "⚠️ سشن قبلاً خارج یا منقضی شده است.",
        "fetching_otp_toast": "🔄 در حال دریافت آخرین کد...",
        "no_new_otp_alert": "⏳ هنوز کد جدیدی نیامده است. چند ثانیه دیگر تلاش کنید.",
        "otp_err_alert": "❌ خطا در دریافت کد.",
        "session_finished_msg": "{yes} <b>سشن با موفقیت بسته و خارج شد.</b>",
        "no_active_order_alert": "⚠️ سفارش فعالی یافت نشد.",
        "bulk_prompt_msg": "{store} <b>خرید سشن {country} ({year})</b>\n\n{pts} <b>قیمت هر سشن:</b> <b>{price} Pts</b>\n{pkg} <b>موجودی:</b> {stock}\n\n👇 <b>به این پیام پاسخ دهید</b> و <b>تعداد سشن</b> را بنویسید.",
        "not_enough_stock_msg": "{warn} <b>موجودی کافی نیست!</b> حداکثر {stock} عدد.",
        "enter_valid_num_msg": "{no} لطفاً یک عدد معتبر وارد کنید.",
        "processing_sessions_msg": "{wait} <b>در حال آماده‌سازی سشن‌ها...</b>",
        "stock_changed_msg": "{no} موجودی تغییر کرد. خرید لغو شد.",
        "bulk_success_caption": "{yes} <b>خرید عمده با موفقیت انجام شد!</b>\n\n{flag} کشور: {country}\n{pkg} تعداد: {qty}\n{pts} مبلغ پرداختی: <b>{cost} Pts</b>\n\n<i>(سشن‌ها به‌صورت امن تحویل داده شدند و ربات فعال نگه نمی‌دارد)</i>",
        "zip_err_msg": "{warn} خطا در ساخت فایل ZIP: {err}",
        "support_msg": "{on} <b>پشتیبانی و اطلاعات Fresh Tg</b>\n\n{warn} برای دریافت راهنمایی با ادمین در ارتباط باشید..",
        "btn_support_url": "📩 پشتیبانی",
        "btn_terms_url": "📜 قوانین و مقررات",
        "btn_channel_url": "📢 کانال",
        "dep_group_unavail": "{warn} <b>گروه واریز تنظیم نشده است</b>\nبا پشتیبانی تماس بگیرید.",
        "dep_menu_msg": "{money} <b>درگاه واریز USDT (امتیاز خودکار)</b>\n━━━━━━━━━━━━━━━━━━━━━━\n{pts} <b>نرخ:</b> <code>$1 USDT = {rate} Points</code>\n{asst} <b>ربات تیپ:</b> <code>@{tip_bot}</code>\n{acc} <b>دریافت‌کننده:</b> <code>@{receiver}</code>\n\n<b>روش واریز:</b>\n1. با دکمه زیر وارد گروه واریز شوید.\n2. دستور زیر را بفرستید (مستقیم یا با ریپلای روی دریافت‌کننده):\n   <code>cc (amount) usdt @{receiver}</code>\n3. پس از تایید <code>@{tip_bot}</code>، امتیازات اضافه شده و ظرف 5 ثانیه از گروه خارج می‌شوید.\n\n{warn} <b>هشدار مهم:</b>\n• واریزهای کمتر از <b>0.5 USDT</b> <b>محاسبه نمی‌شوند</b>. در صورت ارسال کمتر از 0.5 USDT با پشتیبانی تماس بگیرید.\n• اگر ظرف <b>2 دقیقه</b> پس از ورود پیامی نفرستید، به‌طور خودکار خارج می‌شوید.",
        "grp_welcome_msg": "{spark} <b>راهنمای واریز</b> — {mention}\n━━━━━━━━━━━━━━━━━━━━━━\n{money} تیپ خود را بفرستید (مستقیم یا با ریپلای روی دریافت‌کننده):\n<code>cc (deposit amount) usdt @{receiver}</code>\n<i>مثال:</i> <code>cc 5 usdt @{receiver}</code>\n\n{pts} <b>نرخ:</b> <code>$1 USDT = {rate} Points</code>\n\n{warn} <b>قوانین مهم:</b>\n• واریزهای زیر <b>0.5 USDT</b> <b>محاسبه نمی‌شوند</b>. در صورت ارسال کمتر از 0.5 USDT با پشتیبانی تماس بگیرید.\n• ظرف <b>2 دقیقه</b> پیام ارسال کنید در غیر این صورت خارج خواهید شد.",
        "grp_inactive_kick": "{time_e} <a href='tg://user?id={uid}'>کاربر</a> به دلیل 2 دقیقه عدم فعالیت خارج شد.",
        "grp_wrong_token": "{warn} <a href='tg://user?id={uid}'>کاربر</a>، ارز پشتیبانی‌نشده شناسایی شد.\nفقط واریز <b>USDT</b> به‌صورت خودکار ثبت می‌شود—با <b>پشتیبانی</b> تماس بگیرید.",
        "grp_wrong_token_anon": "{warn} ارز پشتیبانی‌نشده شناسایی شد. فقط <b>USDT</b> ثبت می‌شود—با <b>پشتیبانی</b> تماس بگیرید.",
        "grp_min_warn": "{warn} <a href='tg://user?id={uid}'>کاربر</a>، واریز شما <b>{amt} USDT</b> کمتر از حداقل <b>0.5 USDT</b> است.\nواریز زیر <b>0.5 USDT</b> محاسبه نمی‌شود—با <b>پشتیبانی</b> تماس بگیرید.",
        "grp_confirmed": "{yes} <a href='tg://user?id={uid}'>واریز تایید شد</a> — <b>+{pts} Points</b> (${amt:.2f} USDT) اضافه شد.\n<i>خروج از گروه تا 5 ثانیه دیگر...</i>",
        "dm_deposit_credited": "{yes} واریز تایید شد — <b>{pts} Points</b> (${amt:.2f} USDT) به حساب شما اضافه شد.\n{pts} موجودی جدید: <b>{bal} Points</b> | نرخ: $1 = {rate} Points.",
    },
    "tr": {
        "choose_lang_title": "🌐 <b>Dilinizi Seçin</b>",
        "choose_lang_desc": "Bot içinde kullanmak istediğiniz dili seçin.",
        "lang_updated": "✅ Dil <b>Türkçe</b> olarak güncellendi!",
        "lang_set_continue": "✅ Dil <b>Türkçe</b> olarak ayarlandı!",
        "btn_language": "Dil",
        "btn_buy_account": "Hesap Al",
        "btn_my_profile": "Profilim",
        "btn_buy_sessions": "Session Al",
        "btn_deposit": "Yatırım Yap",
        "btn_my_stats": "İstatistiklerim",
        "btn_support": "Destek",
        "btn_admin_panel": "Admin Paneli",
        "btn_choose_lang": "🌐 Dil / Language",
        "btn_join_ch": "📢 Kanala Katıl ({title})",
        "btn_verify_join": "✅ Katılımı Doğrula",
        "btn_read_terms": "📜 Şartları ve Koşulları Oku",
        "btn_accept": "✅ Kabul Et",
        "btn_reject": "❌ Reddet",
        "btn_cancel": "❌ İptal",
        "btn_back": "🔙 Geri",
        "btn_prev": "⬅️ Önceki",
        "btn_next": "➡️ Sonraki",
        "btn_buy_now": "✅ Evet, Şimdi Al",
        "btn_get_otp_again": "🔄 OTP'yi Tekrar Al",
        "btn_logout": "🚪 Bitir ve Çıkış Yap",
        "btn_purchase_logs": "📜 Satın Alma Geçmişi",
        "btn_referral_logs": "👥 Referanslar",
        "btn_join_dep_grp": "🏦 Yatırım Grubuna Katıl",
        "btn_contact_support": "📩 Destek ile İletişime Geç",
        "bot_maintenance": "{off} <b>Bot şu anda bakımda.</b> Lütfen daha sonra tekrar deneyin.",
        "bot_maintenance_alert": "⚙️ Bot bakımda.",
        "slow_down": "⚠️ Lütfen yavaşlayın! Butonlara art arda basmayın.",
        "banned_alert": "🚫 YASAKLANDI",
        "force_join_msg": "{warn} <b>Önce kanallarımıza katılmalısınız!</b>",
        "must_join_alert": "⚠️ Önce kanallara katılmalısınız!",
        "terms_msg": "{doc} <b>ŞARTLAR VE KOŞULLAR</b>\nBotu kullanmadan önce lütfen Şartlar ve Koşulları okuyup kabul edin.",
        "terms_accepted_alert": "✅ Şartlar kabul edildi!",
        "terms_rejected_msg": "{no} Şartları kabul etmeden botu kullanamazsınız.",
        "cancelled_msg": "{no} <b>İptal edildi.</b>",
        "welcome_msg": "👋 <b>Fresh Tg Store'a Hoş Geldiniz!</b>\n\n{pts} <b>Kur:</b> <code>$1 USDT = {rate} Points</code>\n{gift} <b>Davet Et & Kazan:</b>\nArkadaşlarınızı davet edin, yatırımlarının {pct}% kadarını Points olarak kazanın!\n{globe} <code>https://t.me/{bot_user}?start=ref_{ref_uid}</code>",
        "init_error": "⚠️ Hata: hesabınızı başlatmak için /start yazın.",
        "profile_msg": "{acc} <b>KULLANICI PROFİLİ</b>\n\n{id_e} Kullanıcı ID: <code>{uid}</code>\n{pts} Bakiye: <code>{bal} Pts (${usd_bal:.2f})</code>\n{card} Yatırılan: <code>{dep} Pts (${usd_dep:.2f})</code>{disc_msg}\n{cal} Katılım: {joined}\n\n{users} <b>Referans Linkiniz:</b>\n<code>{ref_link}</code>\n\n<i>(Points bonusu kazanmak için linki paylaşın!)</i>",
        "active_discount": "\n{gift} Aktif İndirim: <b>{discount}% OFF</b>",
        "stats_msg": "{stats} <b>İstatistiklerim</b>\n\n{cart} <b>Alınan Hesaplar:</b> {orders}\n{pts} <b>Toplam Harcama:</b> {spent} Pts (${usd_spent:.2f})\n{card} <b>Toplam Yatırım:</b> {dep} Pts (${usd_dep:.2f})",
        "ref_count_alert": "👥 {count} kullanıcı davet ettiniz.",
        "purchase_hist_title": "{doc} <b>Satın Alma Geçmişi (Sayfa {page})</b>\n\n",
        "no_purchases": "Satın alma bulunamadı.",
        "stock_empty": "{no} <b>Stok şu anda boş. Daha sonra tekrar kontrol edin!</b>",
        "bulk_menu": "{store} <b>Toplu Session Menüsü</b>",
        "single_menu": "{cart} <b>Tekli Hesap Menüsü</b>",
        "select_region": "{title}\n\n{globe} <b>Mevcut numaraları görmek için bölge seçin (Sayfa {page}).</b>\n{usdt} Kur: $1 USDT = <b>{rate} Points</b>\n\n",
        "out_of_stock_alert": "❌ Bu ülke için stok tükendi.",
        "out_of_stock_short": "❌ Stok bitti!",
        "select_year_msg": "{cal} <b>Hesap Yılı Seçin</b>\n{globe} Ülke: <b>{country}</b>\n\n",
        "confirm_buy_msg": "{cart} <b>Satın Alımı Onaylayın</b>\n\n{flag} <b>Ülke:</b> {country}\n{cal} <b>Yıl:</b> {year}\n{pts} <b>Son Fiyat:</b> <b>{price} Pts</b> (${usd_price:.2f})\n\n{card} <b>Bakiyeniz:</b> <b>{bal} Pts</b>\n\n❓ Satın alma işlemini onaylıyor musunuz?",
        "sold_out_alert": "❌ Tükendi! Başka bir kullanıcı bu hesabı aldı.",
        "insufficient_bal_alert": "❌ Yetersiz bakiye! {price} Pts gerekli",
        "insufficient_bal_msg": "{no} <b>Yetersiz Bakiye!</b>\n{qty} session almak için <b>{cost} Pts</b> gerekli.",
        "fetching_num": "🔄 <b>Numara alınıyor (+{phone})...</b>",
        "acc_invalid": "{no} <b>Geçersiz hesap.</b> Points iade edildi. Başka bir hesap deneyin.",
        "order_active_msg": "{yes} <b>Sipariş Aktif!</b>\n\n{phone_e} <b>Telefon:</b> <code>{phone}</code>\n{flag} <b>Ülke:</b> {c_icon} {country}\n\n🔻 <b>TALİMATLAR:</b>\n1. Telegram'ı açıp Hesap Ekle seçin\n2. Yukarıdaki numarayı girin.\n3. {wait} <b>Lütfen bekleyin!</b> Bot OTP'yi bekleyip otomatik gönderecektir.\n\n<i>10 dakika içinde OTP gelmezse sipariş iptal olur ve Points iade edilir.</i>",
        "otp_fetched_msg": "{yes} <b>Son OTP Alındı!</b>\n\n{phone_e} <b>Telefon:</b> <code>{phone}</code>\n{flag} <b>Ülke:</b> {c_icon} {country}\n{otp_e} <b>OTP:</b> <code>{code}</code>\n{twofa_line}",
        "twofa_enabled": "{twofa} <b>2FA:</b> <code>{pwd}</code>",
        "twofa_disabled": "🔓 <b>2FA:</b> <code>Kapalı (Şifre yok)</code>",
        "order_expired_msg": "{time_e} <b>Sipariş Süresi Doldu!</b>\n<code>{phone}</code> için 10 dakikalık süre doldu. <b>{price} Pts</b> iade edildi.",
        "session_logged_out_alert": "⚠️ Oturum zaten kapatıldı veya süresi doldu.",
        "fetching_otp_toast": "🔄 Son OTP getiriliyor...",
        "no_new_otp_alert": "⏳ Henüz yeni OTP yok. Birkaç saniye sonra tekrar deneyin.",
        "otp_err_alert": "❌ OTP alınırken hata oluştu.",
        "session_finished_msg": "{yes} <b>Oturum tamamlandı ve çıkış yapıldı.</b>",
        "no_active_order_alert": "⚠️ Aktif sipariş bulunamadı.",
        "bulk_prompt_msg": "{store} <b>{country} ({year}) Session Al</b>\n\n{pts} <b>Session başı fiyat:</b> <b>{price} Pts</b>\n{pkg} <b>Stok:</b> {stock}\n\n👇 Almak istediğiniz <b>session sayısını</b> yazarak bu mesaja yanıt verin.",
        "not_enough_stock_msg": "{warn} <b>Yeterli stok yok!</b> En fazla {stock}.",
        "enter_valid_num_msg": "{no} Lütfen geçerli bir sayı girin.",
        "processing_sessions_msg": "{wait} <b>Session'lar hazırlanıyor...</b>",
        "stock_changed_msg": "{no} İşlem sırasında stok değişti. Alım iptal edildi.",
        "bulk_success_caption": "{yes} <b>Toplu Alım Başarılı!</b>\n\n{flag} Ülke: {country}\n{pkg} Adet: {qty}\n{pts} Toplam Ödenen: <b>{cost} Pts</b>\n\n<i>(Session'lar güvenli şekilde sağlandı, bot aktif tutmaz)</i>",
        "zip_err_msg": "{warn} ZIP oluşturma hatası: {err}",
        "support_msg": "{on} <b>Fresh Tg Destek ve Bilgiler</b>\n\n{warn} Destek için yöneticiyle iletişime geçin..",
        "btn_support_url": "📩 Destek",
        "btn_terms_url": "📜 Şartlar ve Koşullar",
        "btn_channel_url": "📢 Kanal",
        "dep_group_unavail": "{warn} <b>Yatırım grubu ayarlanmamış</b>\nDestek ile iletişime geçin.",
        "dep_menu_msg": "{money} <b>USDT YATIRIM PORTALI (OTO POINTS)</b>\n━━━━━━━━━━━━━━━━━━━━━━\n{pts} <b>Kur:</b> <code>$1 USDT = {rate} Points</code>\n{asst} <b>Tip Botu:</b> <code>@{tip_bot}</code>\n{acc} <b>Alıcı:</b> <code>@{receiver}</code>\n\n<b>Nasıl Yatırılır:</b>\n1. Aşağıdaki butondan Yatırım Grubuna katılın.\n2. Tip gönderin (doğrudan veya alıcıya yanıt vererek):\n   <code>cc (amount) usdt @{receiver}</code>\n3. <code>@{tip_bot}</code> onayladığında Points eklenir ve 5 saniye içinde gruptan çıkarılırsınız.\n\n{warn} <b>Önemli Uyarı:</b>\n• <b>0.5 USDT</b> altındaki yatırımlar <b>sayılmaz</b>. 0.5 USDT'den az gönderdiyseniz Destek ile iletişime geçin.\n• Girdikten sonra <b>2 dakika</b> içinde mesaj göndermezseniz otomatik çıkarılırsınız.",
        "grp_welcome_msg": "{spark} <b>YATIRIM TALİMATLARI</b> — {mention}\n━━━━━━━━━━━━━━━━━━━━━━\n{money} Tip gönderin (doğrudan veya alıcıya yanıt vererek):\n<code>cc (deposit amount) usdt @{receiver}</code>\n<i>Örnek:</i> <code>cc 5 usdt @{receiver}</code>\n\n{pts} <b>Kur:</b> <code>$1 USDT = {rate} Points</code>\n\n{warn} <b>Önemli Kurallar:</b>\n• <b>0.5 USDT</b> altındaki yatırımlar <b>sayılmaz</b>. 0.5 USDT'den az gönderdiyseniz Destek ile iletişime geçin.\n• <b>2 dakika</b> içinde mesaj gönderin, aksi halde çıkarılırsınız.",
        "grp_inactive_kick": "{time_e} <a href='tg://user?id={uid}'>Üye</a> 2 dakika hareketsizlik nedeniyle çıkarıldı.",
        "grp_wrong_token": "{warn} <a href='tg://user?id={uid}'>Üye</a>, desteklenmeyen token algılandı.\nYalnızca <b>USDT</b> yatırımları otomatik işlenir—lütfen <b>Destek</b> ile iletişime geçin.",
        "grp_wrong_token_anon": "{warn} Desteklenmeyen token algılandı. Yalnızca <b>USDT</b> işlenir—lütfen <b>Destek</b> ile iletişime geçin.",
        "grp_min_warn": "{warn} <a href='tg://user?id={uid}'>Üye</a>, <b>{amt} USDT</b> yatırımınız minimum <b>0.5 USDT</b> sınırının altında.\n0.5 USDT altı sayılmaz—lütfen <b>Destek</b> ile iletişime geçin.",
        "grp_confirmed": "{yes} <a href='tg://user?id={uid}'>Yatırım Onaylandı</a> — <b>+{pts} Points</b> (${amt:.2f} USDT) eklendi.\n<i>5 saniye içinde gruptan çıkarılıyorsunuz...</i>",
        "dm_deposit_credited": "{yes} Yatırım Onaylandı — hesabınıza <b>{pts} Points</b> (${amt:.2f} USDT) eklendi.\n{pts} Yeni Bakiye: <b>{bal} Points</b> | Kur: $1 = {rate} Points.",
    },
    "vi": {
        "choose_lang_title": "🌐 <b>Chọn ngôn ngữ của bạn</b>",
        "choose_lang_desc": "Chọn ngôn ngữ bạn muốn sử dụng trong bot.",
        "lang_updated": "✅ Đã đổi ngôn ngữ sang <b>Tiếng Việt</b>!",
        "lang_set_continue": "✅ Đã đặt ngôn ngữ <b>Tiếng Việt</b>!",
        "btn_language": "Ngôn ngữ",
        "btn_buy_account": "Mua Tài Khoản",
        "btn_my_profile": "Hồ Sơ Của Tôi",
        "btn_buy_sessions": "Mua Sessions",
        "btn_deposit": "Nạp Tiền",
        "btn_my_stats": "Thống Kê Của Tôi",
        "btn_support": "Hỗ Trợ",
        "btn_admin_panel": "Bảng Quản Trị",
        "btn_choose_lang": "🌐 Ngôn ngữ / Language",
        "btn_join_ch": "📢 Tham Gia Kênh ({title})",
        "btn_verify_join": "✅ Xác Minh Đã Tham Gia",
        "btn_read_terms": "📜 Đọc Điều Khoản",
        "btn_accept": "✅ Đồng Ý",
        "btn_reject": "❌ Từ Chối",
        "btn_cancel": "❌ Hủy",
        "btn_back": "🔙 Quay Lại",
        "btn_prev": "⬅️ Trước",
        "btn_next": "➡️ Tiếp",
        "btn_buy_now": "✅ Có, Mua Ngay",
        "btn_get_otp_again": "🔄 Lấy Lại OTP",
        "btn_logout": "🚪 Hoàn Tất & Đăng Xuất",
        "btn_purchase_logs": "📜 Lịch Sử Mua",
        "btn_referral_logs": "👥 Giới Thiệu",
        "btn_join_dep_grp": "🏦 Nhóm Nạp Tiền",
        "btn_contact_support": "📩 Liên Hệ Hỗ Trợ",
        "bot_maintenance": "{off} <b>Bot đang bảo trì.</b> Vui lòng thử lại sau.",
        "bot_maintenance_alert": "⚙️ Bot đang bảo trì.",
        "slow_down": "⚠️ Vui lòng thao tác chậm lại! Không bấm liên tục.",
        "banned_alert": "🚫 BỊ CẤM",
        "force_join_msg": "{warn} <b>Bạn cần tham gia các kênh của chúng tôi trước!</b>",
        "must_join_alert": "⚠️ Bạn phải tham gia kênh trước!",
        "terms_msg": "{doc} <b>ĐIỀU KHOẢN SỬ DỤNG</b>\nVui lòng đọc và đồng ý Điều khoản trước khi sử dụng bot.",
        "terms_accepted_alert": "✅ Đã đồng ý điều khoản!",
        "terms_rejected_msg": "{no} Bạn không thể dùng bot nếu chưa đồng ý điều khoản.",
        "cancelled_msg": "{no} <b>Đã hủy.</b>",
        "welcome_msg": "👋 <b>Chào mừng đến với Fresh Tg Store!</b>\n\n{pts} <b>Tỷ giá:</b> <code>$1 USDT = {rate} Points</code>\n{gift} <b>Giới thiệu & Nhận thưởng:</b>\nMời bạn bè và nhận {pct}% tiền nạp của họ bằng Points!\n{globe} <code>https://t.me/{bot_user}?start=ref_{ref_uid}</code>",
        "init_error": "⚠️ Lỗi: hãy bấm /start để khởi tạo tài khoản.",
        "profile_msg": "{acc} <b>HỒ SƠ NGƯỜI DÙNG</b>\n\n{id_e} ID người dùng: <code>{uid}</code>\n{pts} Số dư: <code>{bal} Pts (${usd_bal:.2f})</code>\n{card} Đã nạp: <code>{dep} Pts (${usd_dep:.2f})</code>{disc_msg}\n{cal} Tham gia: {joined}\n\n{users} <b>Link giới thiệu của bạn:</b>\n<code>{ref_link}</code>\n\n<i>(Chia sẻ link cho bạn bè để nhận thưởng Points!)</i>",
        "active_discount": "\n{gift} Giảm giá đang áp dụng: <b>{discount}% OFF</b>",
        "stats_msg": "{stats} <b>Thống Kê Của Tôi</b>\n\n{cart} <b>Tài khoản đã mua:</b> {orders}\n{pts} <b>Tổng đã chi:</b> {spent} Pts (${usd_spent:.2f})\n{card} <b>Tổng đã nạp:</b> {dep} Pts (${usd_dep:.2f})",
        "ref_count_alert": "👥 Bạn đã giới thiệu {count} người dùng.",
        "purchase_hist_title": "{doc} <b>Lịch Sử Mua Hàng (Trang {page})</b>\n\n",
        "no_purchases": "Chưa có giao dịch mua nào.",
        "stock_empty": "{no} <b>Hiện đang hết hàng. Vui lòng quay lại sau!</b>",
        "bulk_menu": "{store} <b>Menu Mua Session Số Lượng Lớn</b>",
        "single_menu": "{cart} <b>Menu Mua Tài Khoản Lẻ</b>",
        "select_region": "{title}\n\n{globe} <b>Chọn khu vực để xem số khả dụng (Trang {page}).</b>\n{usdt} Tỷ giá: $1 USDT = <b>{rate} Points</b>\n\n",
        "out_of_stock_alert": "❌ Hết hàng cho quốc gia này.",
        "out_of_stock_short": "❌ Hết hàng!",
        "select_year_msg": "{cal} <b>Chọn Năm Tạo Tài Khoản</b>\n{globe} Quốc gia: <b>{country}</b>\n\n",
        "confirm_buy_msg": "{cart} <b>Xác Nhận Mua Hàng</b>\n\n{flag} <b>Quốc gia:</b> {country}\n{cal} <b>Năm:</b> {year}\n{pts} <b>Giá cuối:</b> <b>{price} Pts</b> (${usd_price:.2f})\n\n{card} <b>Số dư của bạn:</b> <b>{bal} Pts</b>\n\n❓ Bạn có muốn tiếp tục mua không?",
        "sold_out_alert": "❌ Đã hết! Người khác vừa mua tài khoản này.",
        "insufficient_bal_alert": "❌ Không đủ số dư! Cần {price} Pts",
        "insufficient_bal_msg": "{no} <b>Không đủ số dư!</b>\nBạn cần <b>{cost} Pts</b> để mua {qty} session.",
        "fetching_num": "🔄 <b>Đang lấy số (+{phone})...</b>",
        "acc_invalid": "{no} <b>Tài khoản không hợp lệ.</b> Đã hoàn lại Points. Hãy thử tài khoản khác.",
        "order_active_msg": "{yes} <b>Đơn Hàng Đang Hoạt Động!</b>\n\n{phone_e} <b>Số điện thoại:</b> <code>{phone}</code>\n{flag} <b>Quốc gia:</b> {c_icon} {country}\n\n🔻 <b>HƯỚNG DẪN:</b>\n1. Mở Telegram & chọn Thêm tài khoản\n2. Nhập số ở trên.\n3. {wait} <b>Vui lòng đợi!</b> Bot đang chờ mã OTP và sẽ gửi tự động.\n\n<i>Nếu không có OTP sau 10 phút, đơn sẽ tự hủy và hoàn lại Points.</i>",
        "otp_fetched_msg": "{yes} <b>Đã Lấy OTP Mới Nhất!</b>\n\n{phone_e} <b>Số điện thoại:</b> <code>{phone}</code>\n{flag} <b>Quốc gia:</b> {c_icon} {country}\n{otp_e} <b>OTP:</b> <code>{code}</code>\n{twofa_line}",
        "twofa_enabled": "{twofa} <b>2FA:</b> <code>{pwd}</code>",
        "twofa_disabled": "🔓 <b>2FA:</b> <code>Tắt (Không có mật khẩu)</code>",
        "order_expired_msg": "{time_e} <b>Đơn Hàng Đã Hết Hạn!</b>\nĐã quá 10 phút cho <code>{phone}</code>. <b>{price} Pts</b> của bạn đã được hoàn lại.",
        "session_logged_out_alert": "⚠️ Phiên đã đăng xuất hoặc hết hạn.",
        "fetching_otp_toast": "🔄 Đang kiểm tra OTP mới...",
        "no_new_otp_alert": "⏳ Chưa có OTP mới. Thử lại sau vài giây.",
        "otp_err_alert": "❌ Lỗi khi lấy OTP.",
        "session_finished_msg": "{yes} <b>Đã hoàn tất phiên và đăng xuất thành công.</b>",
        "no_active_order_alert": "⚠️ Không có đơn hàng nào đang hoạt động.",
        "bulk_prompt_msg": "{store} <b>Mua Session {country} ({year})</b>\n\n{pts} <b>Giá mỗi session:</b> <b>{price} Pts</b>\n{pkg} <b>Tồn kho:</b> {stock}\n\n👇 <b>Trả lời tin nhắn này</b> với <b>số lượng session</b> bạn muốn mua.",
        "not_enough_stock_msg": "{warn} <b>Không đủ hàng!</b> Tối đa {stock}.",
        "enter_valid_num_msg": "{no} Vui lòng nhập một số hợp lệ.",
        "processing_sessions_msg": "{wait} <b>Đang xử lý session...</b>",
        "stock_changed_msg": "{no} Tồn kho đã thay đổi khi xử lý. Đã hủy mua.",
        "bulk_success_caption": "{yes} <b>Mua Số Lượng Lớn Thành Công!</b>\n\n{flag} Quốc gia: {country}\n{pkg} Số lượng: {qty}\n{pts} Tổng thanh toán: <b>{cost} Pts</b>\n\n<i>(Session được cung cấp an toàn, bot không giữ hoạt động)</i>",
        "zip_err_msg": "{warn} Lỗi tạo file ZIP: {err}",
        "support_msg": "{on} <b>Hỗ Trợ & Thông Tin Fresh Tg</b>\n\n{warn} Cần hỗ trợ vui lòng liên hệ Admin..",
        "btn_support_url": "📩 Hỗ Trợ",
        "btn_terms_url": "📜 Điều Khoản",
        "btn_channel_url": "📢 Kênh",
        "dep_group_unavail": "{warn} <b>Chưa cấu hình Nhóm Nạp Tiền</b>\nVui lòng liên hệ Hỗ Trợ.",
        "dep_menu_msg": "{money} <b>CỔNG NẠP USDT (TỰ ĐỘNG CỘNG POINTS)</b>\n━━━━━━━━━━━━━━━━━━━━━━\n{pts} <b>Tỷ giá:</b> <code>$1 USDT = {rate} Points</code>\n{asst} <b>Bot nhận tip:</b> <code>@{tip_bot}</code>\n{acc} <b>Người nhận:</b> <code>@{receiver}</code>\n\n<b>Cách nạp tiền:</b>\n1. Tham gia Nhóm Nạp Tiền bằng nút bên dưới.\n2. Gửi tip (trực tiếp hoặc trả lời tin nhắn người nhận):\n   <code>cc (amount) usdt @{receiver}</code>\n3. Khi <code>@{tip_bot}</code> xác nhận, Points sẽ được cộng tự động và bạn sẽ rời nhóm sau 5 giây.\n\n{warn} <b>Lưu ý quan trọng:</b>\n• Nạp dưới <b>0.5 USDT</b> sẽ <b>không</b> được tính. Liên hệ Hỗ Trợ nếu bạn đã gửi dưới 0.5 USDT.\n• Không gửi tin nhắn trong <b>2 phút</b> sau khi vào sẽ bị mời ra khỏi nhóm.",
        "grp_welcome_msg": "{spark} <b>HƯỚNG DẪN NẠP TIỀN</b> — {mention}\n━━━━━━━━━━━━━━━━━━━━━━\n{money} Gửi tip (trực tiếp hoặc trả lời tin nhắn người nhận):\n<code>cc (deposit amount) usdt @{receiver}</code>\n<i>Ví dụ:</i> <code>cc 5 usdt @{receiver}</code>\n\n{pts} <b>Tỷ giá:</b> <code>$1 USDT = {rate} Points</code>\n\n{warn} <b>Quy tắc quan trọng:</b>\n• Nạp dưới <b>0.5 USDT</b> sẽ <b>không</b> được tính. Liên hệ Hỗ Trợ nếu bạn đã gửi dưới 0.5 USDT.\n• Hãy gửi tin nhắn trong vòng <b>2 phút</b>, nếu không bạn sẽ bị xóa khỏi nhóm.",
        "grp_inactive_kick": "{time_e} <a href='tg://user?id={uid}'>Thành viên</a> đã bị xóa do không hoạt động sau 2 phút.",
        "grp_wrong_token": "{warn} <a href='tg://user?id={uid}'>Thành viên</a>, phát hiện token không hỗ trợ.\nChỉ nạp <b>USDT</b> mới được cộng tự động—vui lòng liên hệ <b>Hỗ Trợ</b>.",
        "grp_wrong_token_anon": "{warn} Phát hiện token không hỗ trợ. Chỉ hỗ trợ <b>USDT</b>—vui lòng liên hệ <b>Hỗ Trợ</b>.",
        "grp_min_warn": "{warn} <a href='tg://user?id={uid}'>Thành viên</a>, khoản nạp <b>{amt} USDT</b> thấp hơn mức tối thiểu <b>0.5 USDT</b>.\nNạp dưới <b>0.5 USDT</b> không được tính—vui lòng liên hệ <b>Hỗ Trợ</b>.",
        "grp_confirmed": "{yes} <a href='tg://user?id={uid}'>Đã Xác Nhận Nạp</a> — đã cộng <b>+{pts} Points</b> (${amt:.2f} USDT).\n<i>Xóa khỏi nhóm sau 5 giây...</i>",
        "dm_deposit_credited": "{yes} Nạp Tiền Thành Công — đã cộng <b>{pts} Points</b> (${amt:.2f} USDT) vào tài khoản của bạn.\n{pts} Số dư mới: <b>{bal} Points</b> | Tỷ giá: $1 = {rate} Points.",
    },
}

def get_user_lang(uid: int) -> str:
    try:
        row = cur.execute("SELECT lang FROM users WHERE user_id=?", (uid,)).fetchone()
        if row and row[0] in TRANSLATIONS:
            return row[0]
    except Exception:
        pass
    return "en"

def has_selected_lang(uid: int) -> bool:
    try:
        row = cur.execute("SELECT lang FROM users WHERE user_id=?", (uid,)).fetchone()
        return bool(row and row[0] in TRANSLATIONS)
    except Exception:
        return False

def set_user_lang(uid: int, lang_code: str):
    code = lang_code if lang_code in TRANSLATIONS else "en"
    ensure_user(uid)
    cur.execute("UPDATE users SET lang=? WHERE user_id=?", (code, uid))
    db.commit()

def t(uid: int, key: str, **kwargs) -> str:
    kwargs.pop('uid', None)
    lang = get_user_lang(uid)
    table = TRANSLATIONS.get(lang) or TRANSLATIONS["en"]
    tmpl = table.get(key) or TRANSLATIONS["en"].get(key) or key
    base_ctx = {
        "uid": uid, "ref_uid": uid,
        "yes": P_YES, "no": P_NO, "pkg": P_PKG, "money": P_MONEY, "usdt": P_USDT,
        "pts": P_PTS, "tg": P_TG, "gift": P_GIFT, "stats": P_STATS, "card": P_CARD,
        "users": P_USERS, "cal": P_CAL, "pc": P_PC, "eye": P_EYE, "bank": P_BANK,
        "on": P_ON, "off": P_OFF, "id_e": P_ID, "key_e": P_KEY, "globe": P_GLOBE,
        "cart": P_CART, "store": P_STORE, "otp_e": P_OTP, "twofa": P_2FA,
        "flag": P_FLAG, "phone_e": P_PHONE, "wait": P_WAIT, "time_e": P_TIME,
        "warn": P_WARN, "doc": P_DOC, "sos": P_SOS, "asst": P_ASST, "acc": P_ACC,
        "spark": P_SPARK,
    }
    base_ctx.update(kwargs)
    try:
        return tmpl.format(**base_ctx)
    except Exception:
        return tmpl

def build_language_keyboard(mode: str = "set"):
    """Builds the 10-language inline keyboard matching screenshot `1000084928.png`:
    English | Русский
    فارسی | 中文
    Español | Français
    العربية | Português
    Bahasa Indonesia | हिन्दी
    mode='first' -> sets language and continues onboarding
    mode='switch' -> updates language and shows confirmation/refreshed menu
    """
    rows = []
    for i in range(0, len(SUPPORTED_LANGUAGES), 2):
        r = []
        for code, label in SUPPORTED_LANGUAGES[i:i+2]:
            r.append(styled_inline_btn(label, f"set_lang|{mode}|{code}", style="primary"))
        rows.append(r)
    return rows

async def send_language_menu(event, mode: str = "switch", edit_existing: bool = False):
    uid = event.sender_id
    msg = f"{t(uid, 'choose_lang_title')}\n{t(uid, 'choose_lang_desc')}"
    btns = build_language_keyboard(mode=mode)
    if edit_existing and isinstance(event, events.CallbackQuery.Event):
        try:
            await event.edit(msg, buttons=btns)
            return
        except MessageNotModifiedError:
            return
        except Exception:
            pass
    await bot.send_message(event.chat_id, msg, buttons=btns)

# ================= INITIALIZATION =================
logging.basicConfig(format='%(asctime)s - %(name)s - %(levelname)s - %(message)s', level=logging.INFO)
logger = logging.getLogger(__name__)

os.makedirs("sessions", exist_ok=True)

session_name = f"bot_session_{BOT_TOKEN.split(':')[0]}"
bot = TelegramClient(session_name, API_ID, API_HASH)
bot.parse_mode = 'html'
_patch_telethon_outbound_html()

db = sqlite3.connect("otp_bot_final.db", check_same_thread=False, timeout=20)
db.execute("PRAGMA journal_mode=WAL;")
cur = db.cursor()

active_orders = {}
user_spam_cooldown = {}
session_buy_state = {}
user_locks = {}

# Deposit Group Tracking:
# deposit_group_watchers[uid] = {'joined_at': float, 'has_messaged': bool, 'task': asyncio.Task}
deposit_group_watchers = {}
# Recent `cc <amt> usdt` senders in deposit group as fallback matching: [(timestamp, uid, amount)]
recent_cc_commands = []

def get_user_lock(uid):
    if uid not in user_locks:
        user_locks[uid] = asyncio.Lock()
    return user_locks[uid]

# ================= DATABASE SCHEMA =================
def setup_db():
    cur.executescript("""
    CREATE TABLE IF NOT EXISTS users (
        user_id INTEGER PRIMARY KEY,
        balance INTEGER DEFAULT 0,
        referred_by INTEGER,
        total_deposited INTEGER DEFAULT 0,
        joined_date TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        banned INTEGER DEFAULT 0,
        discount INTEGER DEFAULT 0,
        terms_accepted INTEGER DEFAULT 0,
        lang TEXT DEFAULT NULL
    );
    CREATE TABLE IF NOT EXISTS settings (key TEXT PRIMARY KEY, value TEXT);
    CREATE TABLE IF NOT EXISTS stock (
        phone TEXT PRIMARY KEY,
        session_file TEXT,
        country_name TEXT,
        country_icon TEXT DEFAULT '🌍',
        account_year INTEGER,
        category TEXT DEFAULT 'Good',
        price INTEGER,
        available INTEGER DEFAULT 1,
        twofa TEXT DEFAULT 'None',
        added_date TIMESTAMP DEFAULT CURRENT_TIMESTAMP
    );
    CREATE TABLE IF NOT EXISTS auto_prices (
        country TEXT,
        year TEXT,
        price INTEGER,
        PRIMARY KEY (country, year)
    );
    CREATE TABLE IF NOT EXISTS deposits (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER,
        amount INTEGER,
        method_name TEXT,
        status TEXT,
        date TIMESTAMP DEFAULT CURRENT_TIMESTAMP
    );
    CREATE TABLE IF NOT EXISTS orders (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER,
        country TEXT,
        year INTEGER,
        price INTEGER,
        phone TEXT,
        otp TEXT,
        date TIMESTAMP DEFAULT CURRENT_TIMESTAMP
    );
    CREATE TABLE IF NOT EXISTS admins (
        user_id INTEGER PRIMARY KEY,
        p_add_stock INTEGER DEFAULT 0,
        p_manage_stock INTEGER DEFAULT 0,
        p_stats INTEGER DEFAULT 0,
        p_bal INTEGER DEFAULT 0,
        p_settings INTEGER DEFAULT 0
    );
    CREATE TABLE IF NOT EXISTS custom_countries (
        code TEXT PRIMARY KEY,
        name TEXT,
        flag TEXT
    );
    CREATE TABLE IF NOT EXISTS ui_config (
        key TEXT PRIMARY KEY,
        value TEXT
    );
    """)
    try:
        cur.execute("ALTER TABLE users ADD COLUMN lang TEXT DEFAULT NULL")
        db.commit()
    except Exception:
        pass

setup_db()

# ================= DYNAMIC UI & VARIABLES ENGINE =================
DEFAULT_EMOJIS = {
    "YES": "✅", "NO": "❌", "PKG": "📦", "MONEY": "💰", "USDT": "💲",
    "PTS": "🪙", "TG": "✈️", "GIFT": "🎁", "STATS": "📊", "CARD": "💳",
    "USERS": "👥", "CAL": "📅", "PC": "💻", "EYE": "👁️", "BANK": "🏦",
    "CW": "👛", "ON": "🟢", "OFF": "🔴", "ID": "🆔", "KEY": "⌨️",
    "GLOBE": "🌎", "CART": "🛒", "STORE": "🏬", "OTP": "🔢", "2FA": "🔐",
    "FLAG": "🏳️", "PHONE": "📱", "WAIT": "⏳", "TIME": "⏰", "WARN": "⚠️",
    "DOC": "📃", "SOS": "🆘", "ASST": "🤖", "ACC": "👤", "SPARK": "✨",
    "BELL": "🔔", "BOLT": "⚡", "LOCK": "🔓", "STAR": "⭐", "HUNDRED": "💯", "DIYA": "🪔",
    "FOLDER": "📁", "CALL": "📞", "BACK": "🔙", "PREV": "⬅️", "NEXT": "➡️",
    "REFRESH": "🔄", "LOGOUT": "🚪", "SCROLL": "📜", "PLUS": "➕", "INDEX": "🗂️",
    "MEGAPHONE": "📢", "BAN": "🚫", "LINK": "🔗", "GEAR": "⚙️", "INBOX": "📥",
    "OUTBOX": "📤", "CROWN": "👑", "PALETTE": "🎨", "RULER": "📐", "CLIPBOARD": "📋",
    "TROPHY": "🏆", "EDIT": "✏️", "TRASH": "🗑️", "MEMO": "📝", "ENVELOPE": "📩",
    "NUM1": "1️⃣", "NUM2": "2️⃣", "NUM3": "3️⃣", "NUM4": "4️⃣", "NUM5": "5️⃣",
    "NUM6": "6️⃣", "NUM7": "7️⃣", "NUM8": "8️⃣", "NUM9": "9️⃣", "NUM0": "0️⃣",
    "FLAG_1": "🇺🇸", "FLAG_7": "🇷🇺", "FLAG_20": "🇪🇬", "FLAG_27": "🇿🇦",
    "FLAG_31": "🇳🇱", "FLAG_32": "🇧🇪", "FLAG_33": "🇫🇷", "FLAG_34": "🇪🇸",
    "FLAG_39": "🇮🇹", "FLAG_44": "🇬🇧", "FLAG_46": "🇸🇪", "FLAG_48": "🇵🇱",
    "FLAG_49": "🇩🇪", "FLAG_51": "🇵🇪", "FLAG_52": "🇲🇽", "FLAG_54": "🇦🇷",
    "FLAG_55": "🇧🇷", "FLAG_56": "🇨🇱", "FLAG_57": "🇨🇴", "FLAG_58": "🇻🇪",
    "FLAG_60": "🇲🇾", "FLAG_61": "🇦🇺", "FLAG_62": "🇮🇩", "FLAG_63": "🇵🇭",
    "FLAG_66": "🇹🇭", "FLAG_84": "🇻🇳", "FLAG_86": "🇨🇳", "FLAG_90": "🇹🇷",
    "FLAG_91": "🇮🇳", "FLAG_92": "🇵🇰", "FLAG_93": "🇦🇫", "FLAG_94": "🇱🇰",
    "FLAG_95": "🇲🇲", "FLAG_98": "🇮🇷", "FLAG_212": "🇲🇦", "FLAG_213": "🇩🇿",
    "FLAG_234": "🇳🇬", "FLAG_254": "🇰🇪", "FLAG_255": "🇹🇿", "FLAG_380": "🇺🇦",
    "FLAG_880": "🇧🇩", "FLAG_964": "🇮🇶", "FLAG_966": "🇸🇦", "FLAG_971": "🇦🇪",
    "FLAG_998": "🇺🇿",
}

PREMIUM_EMOJI_MAP = {k: None for k in DEFAULT_EMOJIS}

KEYBOARD_BUTTON_META = {
    "Buy Account": ("🛒", "success", "CART"),
    "My Profile": ("👤", "primary", "ACC"),
    "Buy Sessions": ("📁", "success", "FOLDER"),
    "Deposit": ("💰", "primary", "MONEY"),
    "My Stats": ("📊", "primary", "STATS"),
    "Support": ("📞", None, "CALL"),
    "Language": ("🌐", "primary", "GLOBE"),
    "Admin Panel": ("🔐", "danger", "2FA"),
}

FORCE_JOIN_BUTTON_DEFAULTS = {
    "Join Channel": "primary",
    "Verify Joined": "success",
}

DEFAULT_MENU_LAYOUT = [
    ["Buy Account", "My Profile"],
    ["Buy Sessions"],
    ["Deposit", "My Stats"],
    ["Support"],
    ["Language"],
    ["Admin Panel"]
]

def get_ui_setting(key, default=None):
    row = cur.execute("SELECT value FROM ui_config WHERE key=?", (key,)).fetchone()
    return row[0] if row else default

def set_ui_setting(key, value):
    cur.execute("INSERT OR REPLACE INTO ui_config (key, value) VALUES (?,?)", (key, value))
    db.commit()

def load_ui_config_from_db():
    raw_emojis = get_ui_setting("premium_emojis")
    if raw_emojis:
        try:
            loaded = json.loads(raw_emojis)
            for k, v in loaded.items():
                if k in PREMIUM_EMOJI_MAP:
                    PREMIUM_EMOJI_MAP[k] = v
        except Exception:
            pass

def get_button_color(btn_name: str) -> str | None:
    raw = get_ui_setting("button_colors")
    colors = {}
    if raw:
        try:
            colors = json.loads(raw)
        except Exception:
            colors = {}
    for k, v in colors.items():
        if k.strip().lower() == btn_name.strip().lower():
            return None if v in (None, "", "none") else v
    if btn_name in KEYBOARD_BUTTON_META:
        return KEYBOARD_BUTTON_META[btn_name][1]
    if btn_name in FORCE_JOIN_BUTTON_DEFAULTS:
        return FORCE_JOIN_BUTTON_DEFAULTS[btn_name]
    return None

def get_menu_layout() -> list[list[str]]:
    raw = get_ui_setting("menu_layout")
    if raw:
        try:
            parsed = json.loads(raw)
            if isinstance(parsed, list) and parsed:
                return parsed
        except Exception:
            pass
    return [list(r) for r in DEFAULT_MENU_LAYOUT]

def get_log_channel_id():
    val = get_ui_setting("log_channel_id")
    if val:
        try:
            return int(val)
        except Exception:
            return val
    return LOG_CHANNEL_ID

def get_vouch_channel_id():
    val = get_ui_setting("vouch_channel_id")
    if val:
        try:
            return int(val)
        except Exception:
            return val
    return VOUCH_CHANNEL_ID

def get_deposit_group_id():
    val = get_ui_setting("deposit_group_id")
    if val:
        try:
            return int(val)
        except Exception:
            return val
    return DEPOSIT_GROUP_ID

def get_deposit_group_url() -> str:
    return get_ui_setting("deposit_group_url") or DEPOSIT_GROUP_URL

def get_tip_bot_username() -> str:
    raw = get_ui_setting("tip_bot_username") or DEFAULT_TIP_BOT
    return raw.strip().lstrip("@").lower()

def get_tip_receiver_username() -> str:
    raw = get_ui_setting("tip_receiver_username") or DEFAULT_TIP_RECEIVER
    if raw:
        return raw.strip().lstrip("@")
    # Fallback to username from support URL if t.me/<username>
    sup = get_support_url()
    if "t.me/" in sup:
        cand = sup.split("t.me/", 1)[1].split("/")[0].split("?")[0].strip()
        if cand and not cand.startswith("+"):
            return cand.lstrip("@")
    return "Support"

def get_force_join_channels() -> list[dict]:
    raw = get_ui_setting("force_join_channels")
    if raw:
        try:
            data = json.loads(raw)
            if isinstance(data, list):
                return data
        except Exception:
            pass
    items = []
    for idx, ch in enumerate(CHECK_CHANNELS):
        url = JOIN_URLS[idx] if idx < len(JOIN_URLS) else (JOIN_URLS[-1] if JOIN_URLS else "https://t.me/")
        cid = int(ch) if str(ch).lstrip("-").isdigit() else ch
        items.append({"chat_id": cid, "url": url, "title": f"Channel {idx + 1}"})
    return items

def prem_emoji(key: str, fallback: str) -> str:
    emoji_id = PREMIUM_EMOJI_MAP.get(key)
    if emoji_id:
        eid = str(emoji_id).strip()
        if eid.isdigit():
            return f'<tg-emoji emoji-id="{eid}">{html.escape(fallback)}</tg-emoji>'
    return fallback

def refresh_emoji_globals():
    g = globals()
    for k, fb in DEFAULT_EMOJIS.items():
        g[f"P_{k}"] = prem_emoji(k, fb)
    rebuild_emoji_char_map()

load_ui_config_from_db()
refresh_emoji_globals()

def _build_mtproto_style(style_name: str | None, icon_emoji_id: str | None = None):
    try:
        from telethon.tl import types as _tl_types
        kb_style_cls = getattr(_tl_types, "KeyboardButtonStyle", None)
        if kb_style_cls is None:
            return None
        kwargs = {}
        if style_name == "primary":
            kwargs["bg_primary"] = True
        elif style_name == "success":
            kwargs["bg_success"] = True
        elif style_name == "danger":
            kwargs["bg_danger"] = True
        if icon_emoji_id and str(icon_emoji_id).strip().isdigit():
            kwargs["icon"] = int(str(icon_emoji_id).strip())
        if not kwargs:
            return None
        return kb_style_cls(**kwargs)
    except Exception:
        return None

def _extract_leading_emoji_icon(text: str, explicit_icon_id: str | None = None) -> tuple[str, str | None]:
    if explicit_icon_id and str(explicit_icon_id).strip().isdigit():
        icon_id = str(explicit_icon_id).strip()
        for norm_em in sorted(EMOJI_CHAR_TO_ID.keys(), key=len, reverse=True):
            pat = re.compile(r"^" + "".join(ch + "(?:\ufe0f|\ufe0e)?" for ch in norm_em) + r"\s*")
            if pat.match(text):
                return pat.sub("", text, count=1).strip() or text, icon_id
        return text, icon_id

    if not text or not EMOJI_CHAR_TO_ID:
        return text, None

    for norm_em, eid in sorted(EMOJI_CHAR_TO_ID.items(), key=lambda kv: len(kv[0]), reverse=True):
        pat = re.compile(r"^" + "".join(ch + "(?:\ufe0f|\ufe0e)?" for ch in norm_em) + r"\s*")
        if pat.match(text):
            cleaned = pat.sub("", text, count=1).strip() or text
            return cleaned, eid
    return text, None

def styled_inline_btn(text: str, data: str | bytes, style: str | None = None, icon_emoji_id: str | None = None):
    raw_data = data.encode("utf-8") if isinstance(data, str) else data
    btn_text, resolved_icon = _extract_leading_emoji_icon(text, icon_emoji_id)
    mt_style = _build_mtproto_style(style, resolved_icon)
    if mt_style is not None:
        try:
            from telethon.tl import types as _tl_types
            return _tl_types.KeyboardButtonCallback(text=btn_text, data=raw_data, style=mt_style)
        except Exception:
            pass
    return Button.inline(text, raw_data)

def styled_url_btn(text: str, url: str, style: str | None = None, icon_emoji_id: str | None = None):
    btn_text, resolved_icon = _extract_leading_emoji_icon(text, icon_emoji_id)
    mt_style = _build_mtproto_style(style, resolved_icon)
    if mt_style is not None:
        try:
            from telethon.tl import types as _tl_types
            return _tl_types.KeyboardButtonUrl(text=btn_text, url=url, style=mt_style)
        except Exception:
            pass
    return Button.url(text, url)

def styled_reply_btn(text: str, style: str | None = None, icon_emoji_id: str | None = None):
    btn_text, resolved_icon = _extract_leading_emoji_icon(text, icon_emoji_id)
    mt_style = _build_mtproto_style(style, resolved_icon)
    if mt_style is not None:
        try:
            from telethon.tl import types as _tl_types
            return _tl_types.KeyboardButton(text=btn_text, style=mt_style)
        except Exception:
            pass
    return KeyboardButton(text)

# ================= HELPER FUNCTIONS =================
def is_bot_online():
    res = cur.execute("SELECT value FROM settings WHERE key='bot_status'").fetchone()
    return res[0] == 'on' if res else True

def is_admin(uid):
    if uid == ADMIN_ID: return True
    row = cur.execute("SELECT user_id FROM admins WHERE user_id=?", (uid,)).fetchone()
    return bool(row)

def has_perm(uid, perm):
    if uid == ADMIN_ID: return True
    row = cur.execute(f"SELECT {perm} FROM admins WHERE user_id=?", (uid,)).fetchone()
    return bool(row and row[0] == 1)

def ensure_user(uid):
    cur.execute("INSERT OR IGNORE INTO users (user_id) VALUES (?)", (uid,))
    db.commit()

def get_points_rate() -> float:
    """Returns Points per $1 USDT (default 95.0)."""
    res = cur.execute("SELECT value FROM settings WHERE key='points_rate'").fetchone()
    try:
        return float(res[0]) if res else DEFAULT_POINTS_PER_USD
    except Exception:
        return DEFAULT_POINTS_PER_USD

def get_support_url():
    res = cur.execute("SELECT value FROM settings WHERE key='support_url'").fetchone()
    url = res[0] if res and res[0] else "https://t.me/tgtelehelpbot"
    if not url.startswith("http"): url = "https://" + url.replace("@", "t.me/")
    return url

def to_usd(points) -> float:
    rate = get_points_rate()
    return round(points / rate, 2) if rate > 0 else 0.0

def is_user_banned(uid):
    res = cur.execute("SELECT banned FROM users WHERE user_id=?", (uid,)).fetchone()
    return res and res[0] == 1

def update_balance(uid, amount):
    cur.execute("UPDATE users SET balance = balance + ? WHERE user_id=?", (amount, uid))
    db.commit()

def delete_session_files(session_path):
    base = session_path if not session_path.endswith('.session') else session_path[:-8]
    for ext in ['.session', '.session-wal', '.session-shm', '.session-journal']:
        try:
            if os.path.exists(base + ext): os.remove(base + ext)
        except: pass

async def get_missing_force_join_channels(uid) -> list[dict]:
    """Returns only the force-join channels that `uid` has NOT joined yet."""
    if is_admin(uid):
        return []
    channels = get_force_join_channels()
    if not channels:
        return []
    from telethon.tl.types import PeerChannel
    missing = []
    for ch in channels:
        raw_cid = ch.get("chat_id")
        if raw_cid is None:
            continue
        try:
            entity = None
            try:
                entity = await bot.get_entity(raw_cid)
            except Exception:
                s_cid = str(raw_cid)
                if s_cid.startswith("-100") and s_cid[4:].isdigit():
                    entity = await bot.get_entity(PeerChannel(int(s_cid[4:])))
                elif s_cid.lstrip("-").isdigit():
                    entity = await bot.get_entity(PeerChannel(int(s_cid.lstrip("-"))))
                else:
                    raise
            part_res = await bot(GetParticipantRequest(channel=entity, participant=uid))
            if getattr(part_res, "participant", None) is None:
                missing.append(ch)
        except UserNotParticipantError:
            missing.append(ch)
        except Exception as e:
            err_str = str(e).upper()
            if "USER_NOT_PARTICIPANT" in err_str:
                missing.append(ch)
            else:
                logger.error(f"Channel Check Error ({ch}): {e}")
                continue
    return missing

async def check_channel_joined(uid):
    missing = await get_missing_force_join_channels(uid)
    return len(missing) == 0

async def kick_user_from_deposit_group(chat_id: int, user_id: int):
    """Kicks a user from the deposit group and immediately unbans them so they can rejoin on future deposits."""
    try:
        await bot.kick_participant(chat_id, user_id)
        await asyncio.sleep(0.5)
        try:
            await bot.edit_permissions(chat_id, user_id, view_messages=True)
        except Exception:
            pass
    except Exception as e:
        logger.error(f"Failed to kick user {user_id} from deposit group {chat_id}: {e}")

COUNTRY_CODES = {
    '1': ('USA/Canada', '🇺🇸'), '7': ('Russia', '🇷🇺'), '20': ('Egypt', '🇪🇬'),
    '27': ('South Africa', '🇿🇦'), '31': ('Netherlands', '🇳🇱'), '32': ('Belgium', '🇧🇪'),
    '33': ('France', '🇫🇷'), '34': ('Spain', '🇪🇸'), '39': ('Italy', '🇮🇹'),
    '44': ('UK', '🇬🇧'), '46': ('Sweden', '🇸🇪'), '48': ('Poland', '🇵🇱'),
    '49': ('Germany', '🇩🇪'), '51': ('Peru', '🇵🇪'), '52': ('Mexico', '🇲🇽'),
    '54': ('Argentina', '🇦🇷'), '55': ('Brazil', '🇧🇷'), '56': ('Chile', '🇨🇱'),
    '57': ('Colombia', '🇨🇴'), '58': ('Venezuela', '🇻🇪'), '60': ('Malaysia', '🇲🇾'),
    '61': ('Australia', '🇦🇺'), '62': ('Indonesia', '🇮🇩'), '63': ('Philippines', '🇵🇭'),
    '66': ('Thailand', '🇹🇭'), '84': ('Vietnam', '🇻🇳'), '86': ('China', '🇨🇳'),
    '90': ('Turkey', '🇹🇷'), '91': ('India', '🇮🇳'), '92': ('Pakistan', '🇵🇰'),
    '93': ('Afghanistan', '🇦🇫'), '94': ('Sri Lanka', '🇱🇰'), '95': ('Myanmar', '🇲🇲'),
    '98': ('Iran', '🇮🇷'), '212': ('Morocco', '🇲🇦'), '213': ('Algeria', '🇩🇿'),
    '234': ('Nigeria', '🇳🇬'), '254': ('Kenya', '🇰🇪'), '255': ('Tanzania', '🇹🇿'),
    '380': ('Ukraine', '🇺🇦'), '880': ('Bangladesh', '🇧🇩'), '964': ('Iraq', '🇮🇶'),
    '966': ('Saudi Arabia', '🇸🇦'), '971': ('UAE', '🇦🇪'), '998': ('Uzbekistan', '🇺🇿')
}

def get_flag_by_country_name(name):
    for code, (c_name, c_flag) in COUNTRY_CODES.items():
        if c_name == name: return c_flag
    try:
        row = cur.execute("SELECT flag FROM custom_countries WHERE name=?", (name,)).fetchone()
        if row: return row[0]
    except: pass
    return "🌍"

def get_country_info(phone):
    phone = str(phone).replace(' ', '').replace('+', '')
    if not phone: return "Unknown", "🌍"

    try:
        customs = cur.execute("SELECT code, name, flag FROM custom_countries").fetchall()
        customs.sort(key=lambda x: len(x[0]), reverse=True)
        for code, name, flag in customs:
            if phone.startswith(code): return name, flag
    except: pass

    for length in (3, 2, 1):
        prefix = phone[:length]
        if prefix in COUNTRY_CODES: return COUNTRY_CODES[prefix]
    return "Unknown", "🌍"

async def detect_account_year(client):
    year = 2024
    try:
        try: await client.delete_dialog('TGDNAbot')
        except: pass
        await client.send_message('TGDNAbot', '/start')
        me = await client.get_me()
        await asyncio.sleep(1)
        await client.send_message('TGDNAbot', str(me.id))
        for _ in range(8):
            await asyncio.sleep(1.5)
            msgs = await client.get_messages('TGDNAbot', limit=3)
            for m in msgs:
                if m.text and ('Created:' in m.text or 'Age:' in m.text or 'Registration' in m.text):
                    match = re.search(r'(?:Created|Age|Registration)[^\d]*(\d{4})', m.text, re.IGNORECASE)
                    if match: return int(match.group(1))
    except Exception: pass
    return year

# ================= LOGGING & VOUCH LOGIC =================
async def send_error_log(context_label: str, err: Exception | str):
    try:
        log_ch = get_log_channel_id()
        if not log_ch:
            return
        tb = err if isinstance(err, str) else "".join(traceback.format_exception(type(err), err, err.__traceback__))
        tb_short = html.escape(tb[-2500:])
        t = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        msg = (f"{P_WARN} <b>BOT ERROR LOG</b>\n"
               f"{P_DOC} <b>Context:</b> <code>{html.escape(context_label)}</code>\n"
               f"{P_TIME} <b>Time:</b> {t}\n\n"
               f"<pre>{tb_short}</pre>")
        await bot.send_message(log_ch, msg)
    except Exception as e:
        logger.error(f"Error sending error log: {e}")

async def log_new_user_started(uid, username: str | None, first_name: str | None, ref_id=None):
    try:
        log_ch = get_log_channel_id()
        if not log_ch:
            return
        uname = f"@{html.escape(username)}" if username else "NoUsername"
        fname = html.escape(first_name or "User")
        t = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        ref_line = f"\n{P_GIFT} <b>Referred By:</b> <code>{ref_id}</code>" if ref_id else ""
        msg = (f"{P_USERS} <b>NEW USER STARTED BOT</b>\n\n"
               f"{P_ACC} <b>Name:</b> {fname}\n"
               f"{P_ID} <b>User ID:</b> <code>{uid}</code>\n"
               f"👤 <b>Username:</b> {uname}{ref_line}\n"
               f"{P_TIME} <b>Time:</b> {t}")
        await bot.send_message(log_ch, msg)
    except Exception as e:
        logger.error(f"New User Log Err: {e}")

async def send_vouch_deposit(uid, pts_amt, usdt_amt, method):
    try:
        vouch_ch = get_vouch_channel_id()
        if not vouch_ch:
            return
        masked_uid = f"{str(uid)[:3]}***{str(uid)[-2:]}" if len(str(uid)) >= 5 else str(uid)
        t = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        msg = (f"{P_YES} <b>NEW DEPOSIT VOUCH</b>\n\n"
               f"{P_ACC} <b>User:</b> <code>{masked_uid}</code>\n"
               f"{P_PTS} <b>Points Added:</b> <b>{pts_amt} Pts</b> (${usdt_amt:.2f} USDT)\n"
               f"{P_CARD} <b>Method:</b> {html.escape(str(method))}\n"
               f"{P_TIME} <b>Time:</b> {t}\n\n"
               f"<i>Thank you for trusting Fresh Tg Store!</i>")
        await bot.send_message(vouch_ch, msg)
    except Exception as e:
        logger.error(f"Vouch Dep Err: {e}")

async def send_vouch_purchase(uid, country, pts_amount, year, qty):
    try:
        vouch_ch = get_vouch_channel_id()
        if not vouch_ch:
            return
        masked_uid = f"{str(uid)[:3]}***{str(uid)[-2:]}" if len(str(uid)) >= 5 else str(uid)
        flag = get_flag_by_country_name(country)
        t = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        msg = (f"{P_CART} <b>NEW PURCHASE VOUCH</b>\n\n"
               f"{P_ACC} <b>Buyer:</b> <code>{masked_uid}</code>\n"
               f"{P_GLOBE} <b>Country:</b> {flag} {html.escape(str(country))}\n"
               f"{P_CAL} <b>Year:</b> {year}\n"
               f"{P_PKG} <b>Quantity:</b> {qty}\n"
               f"{P_PTS} <b>Paid:</b> <b>{pts_amount} Pts</b> (${to_usd(pts_amount):.2f})\n"
               f"{P_TIME} <b>Time:</b> {t}\n\n"
               f"<i>Instant Delivery • Fresh Tg Store</i>")
        await bot.send_message(vouch_ch, msg)
    except Exception as e:
        logger.error(f"Vouch Pur Err: {e}")

async def process_referral_bonus(uid, pts_amount):
    row = cur.execute("SELECT referred_by FROM users WHERE user_id=?", (uid,)).fetchone()
    ref = row[0] if row else None
    if ref:
        pct_row = cur.execute("SELECT value FROM settings WHERE key='ref_percent'").fetchone()
        pct = float(pct_row[0]) if pct_row else 3.0
        if pct > 0:
            bonus = int(pts_amount * (pct / 100))
            if bonus > 0:
                update_balance(ref, bonus)
                try:
                    await bot.send_message(
                        ref,
                        f"{P_GIFT} <b>Referral Bonus!</b>\nYour referral <code>{uid}</code> deposited <b>{pts_amount} Pts</b>.\n{P_YES} You earned <b>{bonus} Pts</b>!"
                    )
                except Exception:
                    pass

async def log_primary_deposit(uid, pts_amt, usdt_amt, method):
    try:
        try:
            user = await bot.get_entity(int(uid))
            username = html.escape(user.username) if user.username else "NoUsername"
        except Exception:
            username = "NoUsername"
        t = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        msg = (f"{P_YES} <b>NEW DEPOSIT SUCCESSFUL</b>\n\n"
               f"{P_ACC} Uꜱᴇʀ ID: <code>{uid}</code>\n"
               f"👤 Uꜱᴇʀɴᴀᴍᴇ: @{username}\n"
               f"{P_USDT} USDT: <b>${usdt_amt:.2f}</b>\n"
               f"{P_PTS} Pᴏɪɴᴛꜱ Aᴅᴅᴇᴅ: <b>{pts_amt} Pts</b>\n"
               f"{P_CARD} Mᴇᴛʜᴏᴅ: {method}\n"
               f"{P_TIME} Tɪᴍᴇ: {t}\n\n"
               f"<i>Tʜᴀɴᴋꜱ Fᴏʀ Dᴇᴘᴏꜱɪᴛ Iɴ Fʀᴇꜱʜ Tɢ!</i>")
        log_ch = get_log_channel_id()
        if log_ch:
            try:
                await bot.send_message(log_ch, msg)
            except Exception as e:
                logger.error(f"Failed Log: {e}")
        await send_vouch_deposit(uid, pts_amt, usdt_amt, method)
    except Exception as e:
        logger.error(f"Global Dep Log Err: {e}")

async def log_primary_purchase(uid, country, price_pts, amount_pts, year, qty):
    try:
        t = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        msg = (f"{P_CART} <b>NEW PURCHASE SUCCESSFUL</b>\n\n"
               f"{P_ID} Uꜱᴇʀ Iᴅ: <code>{uid}</code>\n"
               f"{P_GLOBE} Cᴏᴜɴᴛʀʏ: {country}\n"
               f"{P_PTS} Pʀɪᴄᴇ: {price_pts} Pts\n"
               f"{P_CARD} Tᴏᴛᴀʟ Pᴀɪᴅ: {amount_pts} Pts\n"
               f"{P_CAL} Yᴇᴀʀ: {year}\n"
               f"{P_PKG} Qᴜᴀɴᴛɪᴛʏ: {qty}\n"
               f"{P_TIME} Tɪᴍᴇ: {t}")
        log_ch = get_log_channel_id()
        if log_ch:
            try:
                await bot.send_message(log_ch, msg)
            except Exception:
                pass
        await send_vouch_purchase(uid, country, amount_pts, year, qty)
    except Exception as e:
        logger.error(f"Pur Log Err: {e}")

# ================= MENU HELPERS =================
_KB_KEY_MAP = {
    "Buy Account": "btn_buy_account",
    "My Profile": "btn_my_profile",
    "Buy Sessions": "btn_buy_sessions",
    "Deposit": "btn_deposit",
    "My Stats": "btn_my_stats",
    "Support": "btn_support",
    "Language": "btn_language",
    "Admin Panel": "btn_admin_panel",
}

def _resolve_canonical_kb_name(raw_name: str) -> str | None:
    cleaned = raw_name.strip().lower()
    for canonical in KEYBOARD_BUTTON_META:
        if canonical.lower() == cleaned or canonical.lower() in cleaned:
            return canonical
    # Also match localized labels in any language
    for canonical, tr_key in _KB_KEY_MAP.items():
        for lang_tbl in TRANSLATIONS.values():
            loc_label = lang_tbl.get(tr_key, "").strip().lower()
            if loc_label and (loc_label == cleaned or loc_label in cleaned):
                return canonical
    return None

def get_persistent_menu(uid):
    layout = get_menu_layout()
    rows = []
    has_lang_btn = False
    for row_items in layout:
        btn_row = []
        for item in row_items:
            canonical = _resolve_canonical_kb_name(item)
            if not canonical:
                continue
            if canonical == "Admin Panel" and not is_admin(uid):
                continue
            if canonical == "Language":
                has_lang_btn = True
            emoji_prefix, _default_style, emoji_key = KEYBOARD_BUTTON_META[canonical]
            color_style = get_button_color(canonical)
            tr_key = _KB_KEY_MAP.get(canonical)
            disp_name = t(uid, tr_key) if tr_key else canonical
            label = f"{emoji_prefix} {disp_name}"
            btn_row.append(styled_reply_btn(label, style=color_style, icon_emoji_id=PREMIUM_EMOJI_MAP.get(emoji_key)))
        if btn_row:
            rows.append(btn_row)
    # Ensure Language button is always right above Admin Panel if user customized layout without it
    if not has_lang_btn:
        lang_btn = styled_reply_btn(
            f"🌐 {t(uid, 'btn_language')}",
            style=get_button_color("Language"),
            icon_emoji_id=PREMIUM_EMOJI_MAP.get("GLOBE")
        )
        admin_idx = next((idx for idx, r in enumerate(rows) if any("Admin Panel" in (getattr(b, "text", "") or "") or t(uid, "btn_admin_panel") in (getattr(b, "text", "") or "") for b in r)), None)
        if admin_idx is not None:
            rows.insert(admin_idx, [lang_btn])
        else:
            rows.append([lang_btn])
    return ReplyKeyboardMarkup([KeyboardButtonRow(r) for r in rows], resize=True)


WELCOME_MEDIA_POST_URL = "https://t.me/sexders/130"

async def _resolve_welcome_media():
    """Fetches media from https://t.me/sexders/130 if accessible, else returns None."""
    try:
        msg = await bot.get_messages("sexders", ids=130)
        if msg and getattr(msg, "media", None):
            return msg.media
    except Exception as e:
        logger.warning(f"Could not fetch media from {WELCOME_MEDIA_POST_URL}: {e}")
    return None

async def send_main_menu(event, uid):
    me = await bot.get_me()
    pct_row = cur.execute("SELECT value FROM settings WHERE key='ref_percent'").fetchone()
    pct = pct_row[0] if pct_row else "3"
    rate = get_points_rate()
    rate_disp = int(rate) if rate.is_integer() else rate
    msg = t(
        uid,
        "welcome_msg",
        rate=rate_disp,
        pct=pct,
        bot_user=me.username,
        ref_uid=uid
    )

    media = await _resolve_welcome_media()
    kb = get_persistent_menu(uid)
    if isinstance(event, events.CallbackQuery.Event):
        try: await event.delete()
        except: pass
        if media:
            await bot.send_file(uid, media, caption=msg, buttons=kb)
        else:
            await bot.send_message(uid, msg, buttons=kb)
    else:
        if media:
            await bot.send_file(uid, media, caption=msg, buttons=kb)
        else:
            await event.respond(msg, buttons=kb)

# ================= DEPOSIT GROUP FLOW =================
_recent_group_joins: dict[tuple[int, int], float] = {}

def _safe_msg_text(event) -> str:
    txt = getattr(event, "raw_text", None)
    if isinstance(txt, str) and txt:
        return txt
    txt2 = getattr(event, "text", None)
    if isinstance(txt2, str):
        return txt2
    return ""

async def deposit_menu(event):
    uid = event.sender_id
    dep_grp_id = get_deposit_group_id()
    dep_grp_url = get_deposit_group_url()
    rate = get_points_rate()
    receiver = get_tip_receiver_username()
    tip_bot = get_tip_bot_username()

    if not dep_grp_url and dep_grp_id:
        try:
            ent = await bot.get_entity(dep_grp_id)
            inv = await bot(ExportChatInviteRequest(peer=ent))
            dep_grp_url = getattr(inv, "link", "") or ""
            if dep_grp_url:
                set_ui_setting("deposit_group_url", dep_grp_url)
        except Exception as e:
            logger.error(f"Could not export deposit group link: {e}")

    if not dep_grp_url:
        return await bot.send_message(
            event.chat_id,
            f"{P_WARN} <b>Deposit Group Unavailable</b>\nPlease contact Support for assistance."
        )

    rate_disp = int(rate) if rate.is_integer() else rate
    msg = (
        f"{P_MONEY} <b>PREMIUM USDT DEPOSIT PORTAL</b>\n"
        f"━━━━━━━━━━━━━━━━━━━━━━\n"
        f"{P_PTS} <b>Exchange Rate:</b> <code>$1 USDT = {rate_disp} Points</code>\n"
        f"{P_ASST} <b>Tip Processor:</b> <code>@{html.escape(tip_bot)}</code>\n"
        f"{P_ACC} <b>Tip Recipient:</b> <code>@{html.escape(receiver)}</code>\n\n"
        f"<b>How to Deposit:</b>\n"
        f"1. Join the official Deposit Group using the button below.\n"
        f"2. Send your tip (directly or by replying to the recipient):\n"
        f"   <code>cc (amount) usdt @{html.escape(receiver)}</code>\n"
        f"3. Once <code>@{html.escape(tip_bot)}</code> confirms your tip, Points are credited automatically and you are removed from the group in 5 seconds.\n\n"
        f"{P_WARN} <b>Important Notice:</b>\n"
        f"• Deposits below <b>0.5 USDT</b> will <b>not</b> be counted. If you sent less than 0.5 USDT, please contact Support.\n"
        f"• Idle members who do not send a message within <b>2 minutes</b> of joining are automatically removed."
    )

    btns = [
        [styled_url_btn("🏦 Join Deposit Group", dep_grp_url, style="success", icon_emoji_id=PREMIUM_EMOJI_MAP.get("BANK"))],
        [styled_url_btn("📩 Contact Support", get_support_url(), style="primary", icon_emoji_id=PREMIUM_EMOJI_MAP.get("ENVELOPE"))]
    ]
    await bot.send_message(event.chat_id, msg, buttons=btns)

async def _deposit_group_inactivity_timer(chat_id: int, user_id: int):
    """Waits 2 minutes (120s). If user hasn't sent any message in the group, kicks them."""
    try:
        await asyncio.sleep(120)
        info = deposit_group_watchers.get(user_id)
        if info and not info.get("has_messaged"):
            deposit_group_watchers.pop(user_id, None)
            try:
                await bot.send_message(
                    chat_id,
                    f"{P_TIME} <a href='tg://user?id={user_id}'>Member</a> was removed after 2 minutes of inactivity."
                )
            except Exception:
                pass
            await kick_user_from_deposit_group(chat_id, user_id)
    except asyncio.CancelledError:
        pass
    except Exception as e:
        logger.error(f"Inactivity timer err: {e}")

async def _delayed_kick_after_deposit(chat_id: int, user_id: int, delay: int = 5):
    try:
        await asyncio.sleep(delay)
        # Only kick if user hasn't started another active tip session
        watcher = deposit_group_watchers.get(user_id)
        if watcher and watcher.get("pending_tips", 0) > 0:
            return
        deposit_group_watchers.pop(user_id, None)
        await kick_user_from_deposit_group(chat_id, user_id)
    except Exception as e:
        logger.error(f"Delayed kick err: {e}")

@bot.on(events.ChatAction())
async def handle_deposit_group_join(e):
    try:
        dep_grp_id = get_deposit_group_id()
        if not dep_grp_id or e.chat_id != dep_grp_id:
            return
        if not (e.user_joined or e.user_added):
            return

        now = time.time()
        for user in e.users:
            uid = user.id
            if user.bot or is_admin(uid):
                continue

            # Deduplicate identical join events within 10 seconds
            join_key = (dep_grp_id, uid)
            last_join = _recent_group_joins.get(join_key, 0.0)
            if now - last_join < 10.0:
                continue
            _recent_group_joins[join_key] = now

            ensure_user(uid)
            old = deposit_group_watchers.pop(uid, None)
            if old and old.get("task"):
                old["task"].cancel()

            receiver = get_tip_receiver_username()
            rate = get_points_rate()
            rate_disp = int(rate) if rate.is_integer() else rate
            mention = f"<a href='tg://user?id={uid}'>{html.escape(user.first_name or 'Member')}</a>"

            welcome_msg = (
                f"{P_SPARK} <b>DEPOSIT INSTRUCTIONS</b> — {mention}\n"
                f"━━━━━━━━━━━━━━━━━━━━━━\n"
                f"{P_MONEY} Send your tip (directly or by replying to the recipient):\n"
                f"<code>cc (deposit amount) usdt @{html.escape(receiver)}</code>\n"
                f"<i>Example:</i> <code>cc 5 usdt @{html.escape(receiver)}</code>\n\n"
                f"{P_PTS} <b>Rate:</b> <code>$1 USDT = {rate_disp} Points</code>\n\n"
                f"{P_WARN} <b>Important Rules:</b>\n"
                f"• Deposits under <b>0.5 USDT</b> will <b>not</b> be counted. If you sent less than 0.5 USDT, please contact Support.\n"
                f"• Please send a message within <b>2 minutes</b> of joining, or you will be removed automatically."
            )
            await bot.send_message(dep_grp_id, welcome_msg)

            task = asyncio.create_task(_deposit_group_inactivity_timer(dep_grp_id, uid))
            deposit_group_watchers[uid] = {
                "joined_at": now,
                "has_messaged": False,
                "pending_tips": 0,
                "task": task
            }
    except Exception as ex:
        await send_error_log("handle_deposit_group_join", ex)

# ================= BUYING FLOW =================
async def show_countries(event, flow, page=1):
    limit = 10
    offset = (page - 1) * limit

    total_row = cur.execute("SELECT COUNT(DISTINCT country_name) FROM stock WHERE available=1").fetchone()
    total = total_row[0] if total_row else 0
    rows = cur.execute("SELECT country_icon, country_name, COUNT(*) FROM stock WHERE available=1 GROUP BY country_name ORDER BY country_name ASC LIMIT ? OFFSET ?", (limit, offset)).fetchall()

    if not rows and page == 1:
        err_msg = f"{P_NO} <b>Stock is Empty right now. Check back later!</b>"
        if isinstance(event, events.CallbackQuery.Event): return await event.edit(err_msg)
        else: return await event.respond(err_msg)

    title = f"{P_STORE} <b>Bulk Sessions Menu</b>" if flow == 'bulk' else f"{P_CART} <b>Single Account Menu</b>"
    rate = get_points_rate()
    rate_disp = int(rate) if rate.is_integer() else rate
    msg = f"{title}\n\n{P_GLOBE} <b>Select a Region below to view available numbers (Page {page}).</b>\n{P_USDT} Rate: $1 USDT = <b>{rate_disp} Points</b>\n\n"

    btns = []
    for (i, n, c) in rows:
        btns.append([styled_inline_btn(f"{i} {n} ({c})", f"bc|{flow}|{n[:20]}")])

    nav = []
    if page > 1: nav.append(styled_inline_btn("⬅️ Prev", f"pg_c|{flow}|{page-1}"))
    if offset + limit < total: nav.append(styled_inline_btn("➡️ Next", f"pg_c|{flow}|{page+1}"))
    if nav: btns.append(nav)
    btns.append([styled_inline_btn("❌ Cancel", "cancel_action", style="danger", icon_emoji_id=PREMIUM_EMOJI_MAP.get("NO"))])

    if isinstance(event, events.CallbackQuery.Event): await event.edit(msg, buttons=btns)
    else: await event.respond(msg, buttons=btns)

async def show_years(event, flow, country):
    rows = cur.execute("SELECT account_year, price, COUNT(*) FROM stock WHERE available=1 AND country_name LIKE ? GROUP BY account_year, price ORDER BY account_year DESC", (f"{country}%",)).fetchall()
    if not rows: return await event.answer("❌ Out of stock for this country.", alert=True)

    uid = event.sender_id
    disc_row = cur.execute("SELECT discount FROM users WHERE user_id=?", (uid,)).fetchone()
    discount = disc_row[0] if disc_row else 0

    msg = f"{P_CAL} <b>Select Account Year</b>\n{P_GLOBE} Country: <b>{country}</b>\n\n"
    btns = []

    for (y, p, c) in rows:
        disp_p = p if discount == 0 else int(p * (100 - discount) / 100)
        disc_text = f" (-{discount}%)" if discount > 0 else ""
        btns.append([styled_inline_btn(f"📅 {y} | {disp_p} Pts{disc_text} | 📦 {c}", f"by|{flow}|{country}|{y}|{p}")])

    btns.append([styled_inline_btn("🔙 Back to Countries", f"pg_c|{flow}|1")])
    await event.edit(msg, buttons=btns)

async def confirm_purchase(event, country, year, price_str):
    uid = event.sender_id
    base_price = int(price_str)

    bal_row = cur.execute("SELECT balance FROM users WHERE user_id=?", (uid,)).fetchone()
    bal = bal_row[0] if bal_row else 0
    disc_row = cur.execute("SELECT discount FROM users WHERE user_id=?", (uid,)).fetchone()
    discount = disc_row[0] if disc_row else 0
    final_price = base_price if discount == 0 else int(base_price * (100 - discount) / 100)

    msg = (f"{P_CART} <b>Confirm Your Purchase</b>\n\n"
           f"{P_FLAG} <b>Country:</b> {country}\n"
           f"{P_CAL} <b>Year:</b> {year}\n"
           f"{P_PTS} <b>Final Price:</b> <b>{final_price} Pts</b> (${to_usd(final_price):.2f})\n\n"
           f"{P_CARD} <b>Your Balance:</b> <b>{bal} Pts</b>\n\n"
           f"❓ Do you want to proceed with this purchase?")

    btns = [
        [styled_inline_btn("✅ Yes, Buy Now", f"buy_cf|{country}|{year}|{base_price}", style="success", icon_emoji_id=PREMIUM_EMOJI_MAP.get("CART"))],
        [styled_inline_btn("❌ No, Cancel", "cancel_action", style="danger", icon_emoji_id=PREMIUM_EMOJI_MAP.get("NO"))]
    ]
    await event.edit(msg, buttons=btns)

async def process_purchase(event, country, year_str, price_str):
    uid, base_price = event.sender_id, int(price_str)

    disc_row = cur.execute("SELECT discount FROM users WHERE user_id=?", (uid,)).fetchone()
    discount = disc_row[0] if disc_row else 0
    final_price = base_price if discount == 0 else int(base_price * (100 - discount) / 100)

    async with get_user_lock(uid):
        row = cur.execute("SELECT phone, session_file, country_icon, account_year, twofa FROM stock WHERE country_name LIKE ? AND account_year=? AND price=? AND available=1 LIMIT 1", (f"{country}%", int(year_str), base_price)).fetchone()

        if not row:
            return await event.answer("❌ Sold out! Another user just bought this account.", alert=True)

        phone, sess, c_icon, actual_year, twofa_pass = row

        cur.execute("UPDATE users SET balance = balance - ? WHERE user_id=? AND balance >= ?", (final_price, uid, final_price))
        if cur.rowcount == 0:
            return await event.answer(f"❌ Insufficient Balance! Need {final_price} Pts", alert=True)

        cur.execute("UPDATE stock SET available=0 WHERE phone=?", (phone,))
        db.commit()

    await event.edit(f"🔄 <b>Fetching Number (+{phone})...</b>")
    clean_sess = sess if not sess.endswith(".session") else sess[:-8]
    client = TelegramClient(clean_sess, API_ID, API_HASH)

    try:
        await client.connect()
        if not await client.is_user_authorized(): raise Exception("Session dead")
    except Exception:
        async with get_user_lock(uid):
            cur.execute("DELETE FROM stock WHERE phone=?", (phone,))
            cur.execute("UPDATE users SET balance = balance + ? WHERE user_id=?", (final_price, uid))
            db.commit()
        await client.disconnect()
        delete_session_files(sess)
        return await event.edit(f"{P_NO} <b>Account Invalid.</b> Points refunded. Try buying another.")

    msg = (f"{P_YES} <b>Order Active!</b>\n\n"
           f"{P_PHONE} <b>Phone:</b> <code>{phone}</code>\n"
           f"{P_FLAG} <b>Country:</b> {c_icon} {country}\n\n"
           f"🔻 <b>INSTRUCTIONS:</b>\n"
           f"1. Open Telegram & Add Account\n"
           f"2. Enter the number above.\n"
           f"3. {P_WAIT} <b>Please wait!</b> The bot is actively listening for your OTP and will send it automatically once Telegram delivers it.\n\n"
           f"<i>Note: If no OTP is received within 10 minutes, the bot will auto-cancel and refund your Points automatically.</i>")

    sent_msg = await event.edit(msg)

    active_orders[phone] = {
        'uid': uid,
        'client': client, 'sess': sess, 'start_time': time.time(),
        'paid': False, 'price': final_price, 'country': country, 'year': actual_year,
        'c_icon': c_icon, 'twofa': twofa_pass, 'msg_id': sent_msg.id
    }
    asyncio.create_task(auto_otp_task(phone))

async def auto_otp_task(phone):
    if phone not in active_orders: return

    order = active_orders[phone]
    client = order['client']
    start_time = order['start_time']
    uid = order['uid']
    msg_id = order['msg_id']

    while time.time() - start_time < AUTO_CANCEL_SECONDS:
        if phone not in active_orders: return
        try:
            msgs = await client.get_messages(777000, limit=5)
            code = None
            for m in msgs:
                if m.date.timestamp() > start_time - 10:
                    if m.message and re.search(OTP_REGEX, m.message) and "Login detected" not in m.message:
                        code = re.search(OTP_REGEX, m.message).group()
                        break

            if code:
                if not order['paid']:
                    order['paid'] = True
                    async with get_user_lock(uid):
                        cur.execute("INSERT INTO orders (user_id, country, year, price, phone, otp) VALUES (?,?,?,?,?,?)", (uid, order['country'], order['year'], order['price'], phone, code))
                        cur.execute("DELETE FROM stock WHERE phone=?", (phone,))
                        db.commit()

                    await log_primary_purchase(uid, order['country'], order['price'], order['price'], order['year'], 1)

                twofa_text = f"{P_2FA} <b>2FA:</b> <code>{order['twofa']}</code>" if order['twofa'] != "None" else f"🔓 <b>2FA:</b> <code>Disabled (No Password)</code>"
                msg_text = (f"{P_YES} <b>Latest OTP Fetched!</b>\n\n"
                            f"{P_PHONE} <b>Phone:</b> <code>{phone}</code>\n"
                            f"{P_FLAG} <b>Country:</b> {order['c_icon']} {order['country']}\n"
                            f"{P_OTP} <b>OTP:</b> <code>{code}</code>\n"
                            f"{twofa_text}")

                try:
                    await bot.edit_message(uid, msg_id, msg_text, buttons=[[styled_inline_btn("🔄 Get OTP Again", f"get_otp_again|{phone}", style="primary", icon_emoji_id=PREMIUM_EMOJI_MAP.get("OTP"))], [styled_inline_btn("🚪 Finish & Logout", f"logout_bot|{phone}", style="danger", icon_emoji_id=PREMIUM_EMOJI_MAP.get("OFF"))]])
                except MessageNotModifiedError: pass
                except Exception:
                    await bot.send_message(uid, msg_text, buttons=[[styled_inline_btn("🔄 Get OTP Again", f"get_otp_again|{phone}", style="primary", icon_emoji_id=PREMIUM_EMOJI_MAP.get("OTP"))], [styled_inline_btn("🚪 Finish & Logout", f"logout_bot|{phone}", style="danger", icon_emoji_id=PREMIUM_EMOJI_MAP.get("OFF"))]])
                return
        except Exception: pass
        await asyncio.sleep(6)

    if phone in active_orders and not active_orders[phone]['paid']:
        order = active_orders.pop(phone)
        try: await order['client'].disconnect()
        except: pass

        async with get_user_lock(uid):
            cur.execute("UPDATE users SET balance = balance + ? WHERE user_id=?", (order['price'], uid))
            cur.execute("UPDATE stock SET available=1 WHERE phone=?", (phone,))
            db.commit()

        try: await bot.edit_message(uid, msg_id, f"{P_TIME} <b>Order Expired!</b>\nThe 10-minute limit for <code>{phone}</code> ran out. Your Points (<b>{order['price']} Pts</b>) have been automatically refunded.")
        except: pass

async def init_session_purchase(event, country, year, price_str):
    uid, price = event.sender_id, int(price_str)
    stock_row = cur.execute("SELECT COUNT(*) FROM stock WHERE country_name LIKE ? AND account_year=? AND price=? AND available=1", (f"{country}%", int(year), price)).fetchone()
    stock = stock_row[0] if stock_row else 0
    if stock == 0: return await event.answer("❌ Out of stock!", alert=True)

    session_buy_state[uid] = {'country': country, 'year': year, 'price': price, 'stock': stock}
    disc_row = cur.execute("SELECT discount FROM users WHERE user_id=?", (uid,)).fetchone()
    discount = disc_row[0] if disc_row else 0
    p_disp = price if discount == 0 else int(price * (100 - discount) / 100)

    msg = (f"{P_STORE} <b>Buy {country} ({year}) Sessions</b>\n\n"
           f"{P_PTS} <b>Price per session:</b> <b>{p_disp} Pts</b>\n"
           f"{P_PKG} <b>Available Stock:</b> {stock}\n\n"
           f"👇 <b>Reply to this message</b> with the <b>Number of Sessions</b> you want to buy.")
    await event.edit(msg, buttons=[[styled_inline_btn("❌ Cancel", "cancel_action", style="danger", icon_emoji_id=PREMIUM_EMOJI_MAP.get("NO"))]])

async def process_bulk_sessions(event, uid, qty, state, final_cost):
    country, year, price = state['country'], int(state['year']), int(state['price'])
    await event.respond(f"{P_WAIT} <b>Processing your sessions...</b>")

    async with get_user_lock(uid):
        rows = cur.execute("SELECT phone, session_file, twofa, account_year FROM stock WHERE country_name LIKE ? AND account_year=? AND price=? AND available=1 LIMIT ?", (f"{country}%", year, price, qty)).fetchall()
        if len(rows) < qty:
            return await event.respond(f"{P_NO} Stock changed during processing. Purchase Cancelled.")

        cur.execute("UPDATE users SET balance = balance - ? WHERE user_id=? AND balance >= ?", (final_cost, uid, final_cost))
        if cur.rowcount == 0:
            return await event.respond(f"{P_NO} Insufficient Balance! Purchase Cancelled.")

        phones = [r[0] for r in rows]
        placeholders = ",".join("?" for _ in phones)
        cur.execute(f"UPDATE stock SET available=0 WHERE phone IN ({placeholders})", phones)

        price_per_acc = final_cost // qty
        for p in phones:
            cur.execute("INSERT INTO orders (user_id, country, price, phone, otp) VALUES (?,?,?,?,?)", (uid, country, price_per_acc, p, "SESSION_FILES"))
        db.commit()

    zip_name = f"sessions_{uid}_{int(time.time())}.zip"
    numbers_txt = ""

    try:
        with zipfile.ZipFile(zip_name, 'w') as zf:
            for phone, sess_file, twofa_pass, y in rows:
                base_s = sess_file if not sess_file.endswith(".session") else sess_file[:-8]
                for ext in ['.session', '.session-wal', '.session-shm', '.session-journal']:
                    src = base_s + ext
                    if os.path.exists(src): zf.write(src, os.path.basename(src))

                pass_text = twofa_pass if twofa_pass != "None" else "No_Password"
                numbers_txt += f"+{phone} | pass:{pass_text}\n"

            numbers_txt += "\n\nPurchased from @Freshtgsales\n"
            zf.writestr("numbers.txt", numbers_txt)

        caption = f"{P_YES} <b>Bulk Purchase Successful!</b>\n\n{P_FLAG} Country: {country}\n{P_PKG} Quantity: {qty}\n{P_PTS} Total Paid: <b>{final_cost} Pts</b>\n\n<i>(Note: Sessions are safely provided, the bot does not keep them active)</i>"
        await bot.send_file(uid, zip_name, caption=caption)
        await log_primary_purchase(uid, country, price, final_cost, year, qty)
    except Exception as e:
        await send_error_log("process_bulk_sessions", e)
        await event.respond(f"{P_WARN} Error creating zip: {e}")
    finally:
        if os.path.exists(zip_name): os.remove(zip_name)

# ================= STATS & PROFILE FUNCTIONS =================
async def profile_handler(event):
    uid = event.sender_id
    row = cur.execute("SELECT balance, total_deposited, joined_date, discount FROM users WHERE user_id=?", (uid,)).fetchone()
    if not row: return await bot.send_message(event.chat_id, t(uid, "init_error"))

    bal, dep, date, discount = row
    me = await bot.get_me()
    ref_link = f"https://t.me/{me.username}?start=ref_{uid}"
    disc_msg = t(uid, "active_discount", discount=discount) if discount > 0 else ""

    msg = t(
        uid,
        "profile_msg",
        ref_uid=uid,
        bal=bal,
        usd_bal=to_usd(bal),
        dep=dep,
        usd_dep=to_usd(dep),
        disc_msg=disc_msg,
        joined=(date or "")[:10],
        ref_link=ref_link
    )
    await bot.send_message(event.chat_id, msg)

async def stats_handler(event, is_callback=False):
    uid = event.sender_id
    row = cur.execute("SELECT total_deposited FROM users WHERE user_id=?", (uid,)).fetchone()
    if not row: return
    dep = row[0]
    o_row = cur.execute("SELECT COUNT(*), SUM(price) FROM orders WHERE user_id=?", (uid,)).fetchone()
    total_orders = o_row[0] if o_row else 0
    spent = o_row[1] if o_row and o_row[1] else 0

    msg = t(
        uid,
        "stats_msg",
        orders=total_orders,
        spent=spent,
        usd_spent=to_usd(spent),
        dep=dep,
        usd_dep=to_usd(dep)
    )

    btns = [
        [styled_inline_btn(t(uid, "btn_purchase_logs"), "page_purchases_1")],
        [styled_inline_btn(t(uid, "btn_referral_logs"), "view_referrals")]
    ]
    if is_callback:
        try: await event.edit(msg, buttons=btns)
        except MessageNotModifiedError: pass
    else: await bot.send_message(event.chat_id, msg, buttons=btns)

async def send_purchase_page(event, uid, page):
    limit = 5
    offset = (page - 1) * limit
    t_row = cur.execute("SELECT COUNT(*) FROM orders WHERE user_id=?", (uid,)).fetchone()
    total = t_row[0] if t_row else 0
    rows = cur.execute("SELECT phone, date FROM orders WHERE user_id=? ORDER BY id DESC LIMIT ? OFFSET ?", (uid, limit, offset)).fetchall()

    msg = t(uid, "purchase_hist_title", page=page)
    if not rows: msg += t(uid, "no_purchases")
    else:
        for ph, d in rows:
            try:
                dt = datetime.strptime(d, "%Y-%m-%d %H:%M:%S")
                d_str = dt.strftime("%a %b %d %H:%M:%S %Y")
            except:
                d_str = d
            msg += f"{P_PHONE} {ph}\n{P_CAL} {d_str}\n────────────────\n"

    nav = []
    if page > 1: nav.append(styled_inline_btn(t(uid, "btn_prev"), f"page_purchases_{page-1}"))
    nav.append(styled_inline_btn(t(uid, "btn_back"), "back_to_stats"))
    if offset + limit < total: nav.append(styled_inline_btn(t(uid, "btn_next"), f"page_purchases_{page+1}"))
    await event.edit(msg, buttons=[nav])

async def view_referrals(event):
    uid = event.sender_id
    refs = cur.execute("SELECT user_id FROM users WHERE referred_by=?", (uid,)).fetchall()
    await event.answer(t(uid, "ref_count_alert", count=len(refs)), alert=True)

# ================= ADMIN ACTIONS =================
async def admin_panel_handler(event):
    uid = event.sender_id
    if not is_admin(uid): return

    status_text = "🟢 Bot is ON" if is_bot_online() else "🔴 Bot is OFF"
    btns = []

    if uid == ADMIN_ID or has_perm(uid, 'p_settings'):
        btns.append([styled_inline_btn(f"⚡ Status: {status_text}", "adm_togglebot")])

    r1 = []
    if uid == ADMIN_ID or has_perm(uid, 'p_add_stock'):
        r1.extend([styled_inline_btn("➕ Add Single Acc", "adm_addstock"), styled_inline_btn("📦 Add ZIP", "adm_addzip")])
    if r1: btns.append(r1)

    r2 = []
    if uid == ADMIN_ID or has_perm(uid, 'p_manage_stock'):
        r2.extend([styled_inline_btn("🗂️ Manage Stock", "adm_managestock"), styled_inline_btn("🤖 Auto Price", "adm_autoprice")])
    if r2: btns.append(r2)

    r3 = []
    if uid == ADMIN_ID or has_perm(uid, 'p_stats'):
        r3.extend([styled_inline_btn("📊 Statistics", "adm_stats"), styled_inline_btn("📢 Broadcast", "adm_bcast")])
        r3.append(styled_inline_btn("👤 User Info", "adm_userinfo"))
    if r3: btns.append(r3)

    r4 = []
    if uid == ADMIN_ID or has_perm(uid, 'p_bal'):
        r4.extend([styled_inline_btn("🪙 Change Points", "adm_bal"), styled_inline_btn("🚫 Ban User", "adm_ban")])
    if r4: btns.append(r4)

    r5 = []
    if uid == ADMIN_ID or has_perm(uid, 'p_settings'):
        r5.extend([styled_inline_btn("🎁 Discount", "adm_discount"), styled_inline_btn("👥 Ref %", "adm_refpct")])
        btns.append(r5)
        btns.append([styled_inline_btn("🔗 Support URL", "adm_supporturl"), styled_inline_btn("🪙 Set Points Rate", "adm_ptsrate")])
        btns.append([styled_inline_btn("⚙️ Change Variables", "adm_changevars")])
        btns.append([styled_inline_btn("📥 Backup Users", "adm_backupusr"), styled_inline_btn("📤 Restore Users", "adm_restoreusr")])

    if uid == ADMIN_ID:
        btns.append([styled_inline_btn("👑 Manage Admins", "adm_manageadmins")])

    await bot.send_message(event.chat_id, f"{P_PC} <b>ADVANCED ADMIN DASHBOARD</b>", buttons=btns)

async def send_force_join_manage_menu(event):
    chs = get_force_join_channels()
    lines = ["📢 <b>Force Join Chats</b>\n"]
    if not chs:
        lines.append("<i>No force-join channels configured yet.</i>")
    else:
        for ch in chs:
            title = html.escape(str(ch.get("title") or "Channel"))
            cid = html.escape(str(ch.get("chat_id") or ""))
            url = html.escape(str(ch.get("url") or ""))
            lines.append(f"• <b>{title}</b>\n  ID: <code>{cid}</code>\n  Link: {url}\n")

    btns = [
        [styled_inline_btn("+ Add Force Join", "adm_fj_add", style="success", icon_emoji_id=PREMIUM_EMOJI_MAP.get("PLUS"))]
    ]
    for idx, ch in enumerate(chs):
        short_title = str(ch.get("title") or f"Channel {idx+1}")[:22]
        btns.append([styled_inline_btn(f"- Remove {short_title}", f"adm_fj_rem|{idx}", style="danger", icon_emoji_id=PREMIUM_EMOJI_MAP.get("NO"))])
    btns.append([styled_inline_btn("← Back", "adm_changevars", style="danger", icon_emoji_id=PREMIUM_EMOJI_MAP.get("BACK"))])

    msg = "\n".join(lines).strip()
    if isinstance(event, events.CallbackQuery.Event):
        try:
            await event.edit(msg, buttons=btns)
            return
        except MessageNotModifiedError:
            return
        except Exception:
            pass
    await bot.send_message(event.chat_id, msg, buttons=btns)

async def send_change_variables_menu(event):
    msg = (f"{P_PC} <b>CHANGE VARIABLES & UI SETTINGS</b>\n\n"
           f"Select a variable category below to customize live without restarting:")
    btns = [
        [styled_inline_btn("🎨 Change Button Colour", "adm_cv_btncolor"), styled_inline_btn("📐 Change Button Position", "adm_cv_btnpos")],
        [styled_inline_btn("✨ Change Emoji ID", "adm_cv_emoji"), styled_inline_btn("📢 Change Force Join Channel", "adm_cv_fjoin")],
        [styled_inline_btn("📋 Change Logs Channel", "adm_cv_logch"), styled_inline_btn("🏆 Change Vouch Channel", "adm_cv_vouchch")],
        [styled_inline_btn("🏦 Change Deposit Group", "adm_cv_depgrp"), styled_inline_btn("🤖 Change Tip Bot", "adm_cv_tipbot")],
        [styled_inline_btn("👤 Change Tip Receiver", "adm_cv_tiprecv")],
        [styled_inline_btn("🔙 Back to Admin", "adm_adminmain")]
    ]
    await event.edit(msg, buttons=btns)

async def manage_admins_menu(event):
    rows = cur.execute("SELECT user_id FROM admins").fetchall()
    msg = f"{P_USERS} <b>Manage Sub-Admins</b>\n\n"
    for r in rows: msg += f"{P_ACC} <code>{r[0]}</code>\n"
    btns = [[styled_inline_btn("➕ Add Admin", "adm_addadmin"), styled_inline_btn("✏️ Edit Admin", "adm_editadminreq")],
            [styled_inline_btn("🔙 Back", "adm_adminmain")]]
    await event.edit(msg, buttons=btns)

async def edit_admin_menu(event, target_id):
    row = cur.execute("SELECT p_add_stock, p_manage_stock, p_stats, p_bal, p_settings FROM admins WHERE user_id=?", (target_id,)).fetchone()
    if not row: return await event.answer("Admin not found", alert=True)
    p = ["✅" if x==1 else "❌" for x in row]

    btns = [
        [styled_inline_btn(f"➕ Add Stock: {p[0]}", f"adm_tglperm|{target_id}|p_add_stock")],
        [styled_inline_btn(f"🗂️ Manage Stock: {p[1]}", f"adm_tglperm|{target_id}|p_manage_stock")],
        [styled_inline_btn(f"📊 Stats & Bcast: {p[2]}", f"adm_tglperm|{target_id}|p_stats")],
        [styled_inline_btn(f"🪙 Points & Users: {p[3]}", f"adm_tglperm|{target_id}|p_bal")],
        [styled_inline_btn(f"⚙️ Settings: {p[4]}", f"adm_tglperm|{target_id}|p_settings")],
        [styled_inline_btn("🗑️ Remove Admin", f"adm_deladmin|{target_id}", style="danger")],
        [styled_inline_btn("🔙 Back", "adm_manageadmins")]
    ]
    await event.edit(f"✏️ <b>Editing Admin:</b> <code>{target_id}</code>", buttons=btns)

async def send_manage_stock_page(event, page):
    limit = 10
    offset = (page - 1) * limit
    rows = cur.execute("SELECT DISTINCT country_name FROM stock ORDER BY country_name").fetchall()
    total = len(rows)
    countries = rows[offset:offset+limit]

    btns = []
    for (c,) in countries:
        flag = get_flag_by_country_name(c)
        btns.append([styled_inline_btn(f"{flag} {c}", f"adm_msc|{c}")])

    nav = []
    if page > 1: nav.append(styled_inline_btn("⬅️ Prev", f"adm_mspg|{page-1}"))
    if offset + limit < total: nav.append(styled_inline_btn("➡️ Next", f"adm_mspg|{page+1}"))
    if nav: btns.append(nav)
    btns.append([styled_inline_btn("🔙 Back", "adm_adminmain")])
    await event.edit(f"{P_DOC} <b>Manage Stock</b> (Page {page})\nSelect a country to edit its properties:", buttons=btns)

async def send_manage_stock_country(event, c_name):
    years = cur.execute("SELECT DISTINCT account_year FROM stock WHERE country_name=? ORDER BY account_year DESC", (c_name,)).fetchall()
    flag = get_flag_by_country_name(c_name)
    btns = [
        [styled_inline_btn("✏️ Edit Country Name", f"adm_msedit|name|{c_name}"), styled_inline_btn("🏳️ Edit Flag", f"adm_msedit|flag|{c_name}")],
        [styled_inline_btn("🪙 Edit Common Price (Pts)", f"adm_msedit|cprice|{c_name}")]
    ]
    y_btns = []
    for (y,) in years: y_btns.append(styled_inline_btn(f"📅 {y}", f"adm_msedit|yprice|{c_name}|{y}"))

    for i in range(0, len(y_btns), 3): btns.append(y_btns[i:i+3])
    btns.append([styled_inline_btn("🔙 Back", "adm_mspg|1")])
    await event.edit(f"{flag} <b>Managing: {c_name}</b>\nSelect an option to edit:", buttons=btns)

async def send_autoprice_page(event, page):
    limit = 10
    offset = (page - 1) * limit
    c_list = set([c[0] for c in COUNTRY_CODES.values()])
    db_countries = cur.execute("SELECT DISTINCT country_name FROM stock").fetchall()
    for (c,) in db_countries: c_list.add(c)

    custom_countries = cur.execute("SELECT DISTINCT name FROM custom_countries").fetchall()
    for (c,) in custom_countries: c_list.add(c)

    c_list = sorted(list(c_list))
    total = len(c_list)
    countries = c_list[offset:offset+limit]

    btns = []
    for c in countries:
        flag = get_flag_by_country_name(c)
        btns.append([styled_inline_btn(f"{flag} {c}", f"adm_apc|{c}")])

    nav = []
    if page > 1: nav.append(styled_inline_btn("⬅️ Prev", f"adm_appg|{page-1}"))
    if offset + limit < total: nav.append(styled_inline_btn("➡️ Next", f"adm_appg|{page+1}"))
    if nav: btns.append(nav)
    btns.append([styled_inline_btn("➕ Add Custom Country", "adm_ap_add_country")])
    btns.append([styled_inline_btn("🔙 Back", "adm_adminmain")])
    await event.edit(f"{P_ASST} <b>Auto Price Setup</b> (Page {page})\nSelect a country to set fixed prices in Points:", buttons=btns)

async def send_autoprice_country(event, c_name):
    flag = get_flag_by_country_name(c_name)
    btns = [[styled_inline_btn("🪙 Set Common Price (Pts)", f"adm_apset|{c_name}|Common")]]
    y_btns = []
    for y in range(2024, 1999, -1): y_btns.append(styled_inline_btn(f"📅 {y}", f"adm_apset|{c_name}|{y}"))
    for i in range(0, len(y_btns), 4): btns.append(y_btns[i:i+4])
    btns.append([styled_inline_btn("🔙 Back", "adm_appg|1")])
    await event.edit(f"{flag} <b>Auto Price: {c_name}</b>\nSelect 'Common' for default price, or specific years:", buttons=btns)

def _parse_channel_target(raw_input: str):
    s = raw_input.strip()
    if s.lstrip("-").isdigit():
        return int(s)
    if s.startswith("https://t.me/") or s.startswith("http://t.me/"):
        part = s.split("t.me/", 1)[1].split("?")[0].strip("/")
        if not part.startswith("+") and not part.startswith("joinchat/"):
            return "@" + part
    if not s.startswith("@") and not s.startswith("http"):
        return "@" + s
    return s

async def admin_actions(event):
    data_full = event.data.decode()
    if not data_full.startswith("adm_"): return
    uid = event.sender_id
    action_data = data_full[4:]
    chat = event.chat_id

    if action_data == "adminmain":
        await event.delete()
        class FakeEvent: chat_id = chat; sender_id = uid
        return await admin_panel_handler(FakeEvent())

    if action_data == "changevars" and has_perm(uid, 'p_settings'):
        return await send_change_variables_menu(event)

    if action_data == "cv_fjoin" and has_perm(uid, 'p_settings'):
        return await send_force_join_manage_menu(event)

    if action_data.startswith("fj_rem|") and has_perm(uid, 'p_settings'):
        try:
            rem_idx = int(action_data.split("|", 1)[1])
            chs = get_force_join_channels()
            if 0 <= rem_idx < len(chs):
                removed = chs.pop(rem_idx)
                set_ui_setting("force_join_channels", json.dumps(chs))
                await event.answer(f"Removed {removed.get('title') or 'channel'}", alert=False)
            else:
                await event.answer("Channel not found", alert=True)
        except Exception as rem_err:
            await event.answer(f"Error: {rem_err}", alert=True)
        return await send_force_join_manage_menu(event)

    if action_data == "togglebot" and has_perm(uid, 'p_settings'):
        new_status = 'off' if is_bot_online() else 'on'
        cur.execute("UPDATE settings SET value=? WHERE key='bot_status'", (new_status,))
        db.commit()
        await event.answer(f"Bot turned {new_status.upper()}", alert=True)
        class FakeEvent: chat_id = chat; sender_id = uid
        await admin_panel_handler(FakeEvent())
        await event.delete()
        return

    elif action_data == "stats" and has_perm(uid, 'p_stats'):
        u_row = cur.execute("SELECT COUNT(*) FROM users").fetchone()
        u = u_row[0] if u_row else 0
        s_row = cur.execute("SELECT COUNT(*) FROM stock WHERE available=1").fetchone()
        s = s_row[0] if s_row else 0
        dep_row = cur.execute("SELECT SUM(total_deposited) FROM users").fetchone()
        total_dep_pts = dep_row[0] if dep_row and dep_row[0] else 0
        bal_row = cur.execute("SELECT SUM(balance) FROM users").fetchone()
        total_bal = bal_row[0] if bal_row and bal_row[0] else 0
        o_row = cur.execute("SELECT COUNT(*), SUM(price) FROM orders").fetchone()
        total_orders = o_row[0] if o_row else 0
        total_spent = o_row[1] if o_row and o_row[1] else 0

        msg = (f"{P_STATS} <b>ADVANCED STATS</b>\n\n"
               f"{P_USERS} <b>Total Users:</b> {u}\n"
               f"{P_PKG} <b>Accounts in Stock:</b> {s}\n"
               f"{P_MONEY} <b>Total Deposited:</b> {total_dep_pts} Pts (${to_usd(total_dep_pts):.2f})\n\n"
               f"{P_CARD} <b>Overall Users Balance:</b> {total_bal} Pts\n"
               f"{P_CART} <b>Total Accounts Sold:</b> {total_orders}\n"
               f"{P_PTS} <b>Overall Sales Amount:</b> {total_spent} Pts (${to_usd(total_spent):.2f})")
        return await event.edit(msg, buttons=[[styled_inline_btn("🔙 Back", "adm_adminmain")]])

    elif action_data == "manageadmins" and uid == ADMIN_ID:
        return await manage_admins_menu(event)

    elif action_data.startswith("tglperm|") and uid == ADMIN_ID:
        _, t_id, p_name = action_data.split("|")
        cur.execute(f"UPDATE admins SET {p_name} = CASE WHEN {p_name}=1 THEN 0 ELSE 1 END WHERE user_id=?", (t_id,))
        db.commit()
        return await edit_admin_menu(event, t_id)

    elif action_data.startswith("deladmin|") and uid == ADMIN_ID:
        t_id = action_data.split("|")[1]
        cur.execute("DELETE FROM admins WHERE user_id=?", (t_id,))
        db.commit()
        await event.answer("✅ Admin Removed", alert=True)
        return await manage_admins_menu(event)

    elif action_data == "managestock" and has_perm(uid, 'p_manage_stock'): return await send_manage_stock_page(event, 1)
    elif action_data.startswith("mspg|") and has_perm(uid, 'p_manage_stock'): return await send_manage_stock_page(event, int(action_data.split("|")[1]))
    elif action_data.startswith("msc|") and has_perm(uid, 'p_manage_stock'): return await send_manage_stock_country(event, action_data.split("|")[1])
    elif action_data == "autoprice" and has_perm(uid, 'p_manage_stock'): return await send_autoprice_page(event, 1)
    elif action_data.startswith("appg|") and has_perm(uid, 'p_manage_stock'): return await send_autoprice_page(event, int(action_data.split("|")[1]))
    elif action_data.startswith("apc|") and has_perm(uid, 'p_manage_stock'): return await send_autoprice_country(event, action_data.split("|")[1])

    elif action_data == "backupusr" and has_perm(uid, 'p_settings'):
        cur.execute("SELECT * FROM users")
        with open("users_backup.csv", "w", newline="", encoding="utf-8") as f:
            w = csv.writer(f); w.writerow([i[0] for i in cur.description]); w.writerows(cur.fetchall())
        await bot.send_file(chat, "users_backup.csv", caption=f"{P_USERS} <b>Users Backup CSV</b>")
        os.remove("users_backup.csv")
        return await event.answer("✅ Backup Generated!", alert=True)

    async with bot.conversation(chat, timeout=600) as conv:
        async def get_reply(txt):
            await conv.send_message(txt + "\n\n<i>(Type /cancel to abort)</i>")
            resp = await conv.get_response()
            if resp.text == "/cancel": raise ValueError("Cancelled")
            return resp

        try:
            # -------- CHANGE VARIABLES HANDLERS --------
            if action_data == "cv_btncolor" and has_perm(uid, 'p_settings'):
                all_names = list(KEYBOARD_BUTTON_META.keys()) + list(FORCE_JOIN_BUTTON_DEFAULTS.keys())
                cur_lines = [f"• <code>{name}</code> → <b>{get_button_color(name) or 'none'}</b>" for name in all_names]
                prompt = (f"🎨 <b>CHANGE BUTTON COLOUR</b>\n\n"
                          f"<b>Available Button Names:</b>\n" + "\n".join(cur_lines) + "\n\n"
                          f"<b>Available Colours:</b> <code>danger</code> (Red), <code>primary</code> (Blue), <code>success</code> (Green), <code>none</code> (Default)\n\n"
                          f"<b>Send bulk lines in this format:</b>\n"
                          f"<code>Buy Account danger\nMy Profile primary\nDeposit success\nJoin Channel primary\nVerify Joined success\nSupport none</code>")
                resp = await get_reply(prompt)
                raw = get_ui_setting("button_colors")
                colors = json.loads(raw) if raw else {}
                updated_log = []
                failed_log = []
                valid_styles = {"danger", "primary", "success", "none"}

                for line in resp.text.strip().splitlines():
                    line = line.strip()
                    if not line:
                        continue
                    parts = line.rsplit(None, 1)
                    if len(parts) != 2:
                        failed_log.append(f"❌ <code>{html.escape(line)}</code> (Invalid format)")
                        continue
                    raw_btn, style_val = parts[0].strip(), parts[1].strip().lower()
                    if style_val not in valid_styles:
                        failed_log.append(f"❌ <code>{html.escape(line)}</code> (Invalid colour '{html.escape(style_val)}')")
                        continue
                    matched_name = None
                    for valid_n in all_names:
                        if valid_n.lower() == raw_btn.lower():
                            matched_name = valid_n
                            break
                    if not matched_name:
                        failed_log.append(f"❌ <code>{html.escape(raw_btn)}</code> (Unknown button name)")
                        continue
                    colors[matched_name] = style_val
                    updated_log.append(f"✅ <b>{matched_name}</b> → <code>{style_val}</code>")

                set_ui_setting("button_colors", json.dumps(colors))
                res_msg = "🎨 <b>Button Colour Update Report:</b>\n\n"
                if updated_log:
                    res_msg += "<b>Updated:</b>\n" + "\n".join(updated_log) + "\n\n"
                if failed_log:
                    res_msg += "<b>Failed:</b>\n" + "\n".join(failed_log)
                await conv.send_message(res_msg, buttons=get_persistent_menu(uid))

            elif action_data == "cv_btnpos" and has_perm(uid, 'p_settings'):
                cur_layout = get_menu_layout()
                cur_preview = "\n".join([" - ".join(r) for r in cur_layout])
                valid_kb = ", ".join([f"<code>{k}</code>" for k in KEYBOARD_BUTTON_META.keys()])
                prompt = (f"📐 <b>CHANGE KEYBOARD BUTTON POSITION</b>\n\n"
                          f"<b>Current Layout:</b>\n<code>{cur_preview}</code>\n\n"
                          f"<b>Valid Keyboard Button Names:</b>\n{valid_kb}\n\n"
                          f"<b>Send new layout using <code>-</code> for same row and new line for next row:</b>\n"
                          f"<code>Buy Account - My Profile\nBuy Sessions\nDeposit - My Stats\nSupport\nAdmin Panel</code>")
                resp = await get_reply(prompt)
                new_layout = []
                unknown_items = []
                for line in resp.text.strip().splitlines():
                    line = line.strip()
                    if not line:
                        continue
                    row_btns = []
                    for piece in line.split("-"):
                        cand = piece.strip()
                        if not cand:
                            continue
                        canon = _resolve_canonical_kb_name(cand)
                        if canon:
                            row_btns.append(canon)
                        else:
                            unknown_items.append(cand)
                    if row_btns:
                        new_layout.append(row_btns)

                if not new_layout:
                    return await conv.send_message(f"{P_NO} No valid buttons found in your layout.")

                set_ui_setting("menu_layout", json.dumps(new_layout))
                preview_new = "\n".join([" - ".join(r) for r in new_layout])
                warn_txt = f"\n\n⚠️ <b>Ignored unknown names:</b> {', '.join(html.escape(x) for x in unknown_items)}" if unknown_items else ""
                await conv.send_message(f"{P_YES} <b>Keyboard Button Position Updated!</b>\n\n<code>{preview_new}</code>{warn_txt}", buttons=get_persistent_menu(uid))

            elif action_data == "cv_emoji" and has_perm(uid, 'p_settings'):
                def _norm_emoji(s: str) -> str:
                    return s.replace("\ufe0f", "").replace("\ufe0e", "").strip()

                normal_to_key = {_norm_emoji(fb): k for k, fb in DEFAULT_EMOJIS.items()}
                _vals = list(DEFAULT_EMOJIS.values())
                emoji_grid = "\n".join("  ".join(_vals[i:i+8]) for i in range(0, len(_vals), 8))
                prompt = (f"✨ <b>CHANGE EMOJI ID (BULK)</b>\n\n"
                          f"<b>Available Normal Emojis:</b>\n{emoji_grid}\n\n"
                          f"<b>Send bulk lines in this format:</b>\n"
                          f"<code>Normal_Emoji Premium_Emoji</code> <i>(or numeric emoji_id)</i>\n\n"
                          f"<b>Example:</b>\n"
                          f"<code>💯 5368324170671202286\n🟢 ✅</code>")
                resp = await get_reply(prompt)
                raw_msg = getattr(resp, "message", None) or resp.text or ""
                entities = getattr(resp, "entities", None) or []

                def _utf16_len(s: str) -> int:
                    return len(s.encode("utf-16-le")) // 2

                custom_entities = []
                for ent in entities:
                    if isinstance(ent, MessageEntityCustomEmoji):
                        custom_entities.append((ent.offset, ent.offset + ent.length, str(ent.document_id)))
                custom_entities.sort(key=lambda x: x[0])

                raw_char_map_str = get_ui_setting("custom_emoji_char_map")
                custom_char_map = json.loads(raw_char_map_str) if raw_char_map_str else {}

                updated_emojis = []
                failed_emojis = []

                lines = raw_msg.splitlines(keepends=True)
                utf16_cursor = 0
                for raw_line in lines:
                    line_u16_start = utf16_cursor
                    line_u16_end = utf16_cursor + _utf16_len(raw_line)
                    utf16_cursor = line_u16_end

                    stripped = raw_line.strip()
                    if not stripped:
                        continue

                    line_customs = [
                        (s, e, doc_id) for (s, e, doc_id) in custom_entities
                        if s >= line_u16_start and s < line_u16_end
                    ]

                    parts = stripped.split(None, 1)
                    if len(parts) == 2:
                        target_token, val_token = parts[0].strip(), parts[1].strip()
                    else:
                        if len(stripped) >= 2 and stripped[1] in ("\ufe0f", "\ufe0e"):
                            target_token = stripped[:2]
                            val_token = stripped[2:].strip()
                        else:
                            target_token = stripped[0]
                            val_token = stripped[1:].strip()

                    if not val_token and not line_customs:
                        failed_emojis.append(f"❌ {html.escape(stripped)} (Missing premium emoji or ID)")
                        continue

                    norm_target = _norm_emoji(target_token)
                    e_key = normal_to_key.get(norm_target)
                    if not e_key and target_token.upper() in DEFAULT_EMOJIS:
                        e_key = target_token.upper()

                    # Extract custom emoji ID from entity on this line, or numeric ID in val_token
                    extracted_id = None
                    if line_customs:
                        extracted_id = line_customs[-1][2]
                    else:
                        # Also check if val_token contains a numeric ID (e.g. digits or `tg://emoji?id=...`)
                        num_m = re.search(r"(\d{6,})", val_token)
                        if num_m:
                            extracted_id = num_m.group(1)

                    if not extracted_id:
                        disp_t = DEFAULT_EMOJIS[e_key] if e_key else html.escape(target_token)
                        failed_emojis.append(f"❌ {disp_t} (Not a valid Telegram Premium Emoji or numeric ID)")
                        continue

                    if e_key:
                        PREMIUM_EMOJI_MAP[e_key] = extracted_id
                        fb = DEFAULT_EMOJIS[e_key]
                        custom_char_map[_norm_emoji(fb)] = extracted_id
                        updated_emojis.append(f'✅ {fb} → <tg-emoji emoji-id="{extracted_id}">{fb}</tg-emoji> (<code>{extracted_id}</code>)')
                    else:
                        custom_char_map[norm_target] = extracted_id
                        updated_emojis.append(f'✅ {html.escape(target_token)} → <tg-emoji emoji-id="{extracted_id}">{html.escape(target_token)}</tg-emoji> (<code>{extracted_id}</code>)')

                set_ui_setting("premium_emojis", json.dumps(PREMIUM_EMOJI_MAP))
                set_ui_setting("custom_emoji_char_map", json.dumps(custom_char_map))
                refresh_emoji_globals()

                report = "✨ <b>Emoji ID Update Report:</b>\n\n"
                if updated_emojis:
                    report += "<b>Updated Emojis:</b>\n" + "\n".join(updated_emojis) + "\n\n"
                if failed_emojis:
                    report += "<b>Failed Emojis:</b>\n" + "\n".join(failed_emojis)
                if not updated_emojis and not failed_emojis:
                    report += "⚠️ Nothing processed."
                await conv.send_message(report)

            elif action_data == "fj_add" and has_perm(uid, 'p_settings'):
                prompt = (
                    f"+ <b>ADD FORCE JOIN CHANNEL</b>\n\n"
                    f"Send Channel Link, Channel ID, or <code>@username</code> (one per line for multiple channels).\n"
                    f"<i>Bot will generate its own invite link automatically (make sure bot is Admin with Invite Users via Link permission).</i>"
                )
                resp = await get_reply(prompt)
                cur_chs = get_force_join_channels()
                existing_ids = {str(c.get("chat_id")) for c in cur_chs}
                logs = []
                added_any = False

                for idx, line in enumerate(resp.text.strip().splitlines(), start=1):
                    raw_item = line.strip()
                    if not raw_item:
                        continue
                    try:
                        target = _parse_channel_target(raw_item)
                        entity = await bot.get_entity(target)
                        chat_id = int(f"-100{entity.id}") if not str(entity.id).startswith("-100") else int(entity.id)
                        title = getattr(entity, "title", None) or f"Channel {idx}"

                        gen_url = None
                        try:
                            inv = await bot(ExportChatInviteRequest(peer=entity))
                            gen_url = getattr(inv, "link", None)
                        except Exception:
                            uname = getattr(entity, "username", None)
                            if uname:
                                gen_url = f"https://t.me/{uname}"
                            elif raw_item.startswith("http"):
                                gen_url = raw_item

                        if not gen_url:
                            logs.append(f"⚠️ <b>{html.escape(title)}</b> (<code>{chat_id}</code>): Could not generate invite link (Make bot Admin with Invite permission).")
                            continue

                        entry = {"chat_id": chat_id, "url": gen_url, "title": title}
                        if str(chat_id) in existing_ids:
                            cur_chs = [entry if str(c.get("chat_id")) == str(chat_id) else c for c in cur_chs]
                        else:
                            cur_chs.append(entry)
                            existing_ids.add(str(chat_id))
                        added_any = True
                        logs.append(f"✅ <b>{html.escape(title)}</b> (<code>{chat_id}</code>)\n🔗 Link: <code>{gen_url}</code>")
                    except Exception as ch_err:
                        logs.append(f"❌ <code>{html.escape(raw_item)}</code>: {html.escape(str(ch_err))}")

                if added_any:
                    set_ui_setting("force_join_channels", json.dumps(cur_chs))
                await conv.send_message("\n\n".join(logs) if logs else "⚠️ Nothing added.")
                await send_force_join_manage_menu(event)

            elif action_data == "cv_logch" and has_perm(uid, 'p_settings'):
                cur_log = get_log_channel_id()
                resp = await get_reply(f"📋 <b>CHANGE LOGS CHANNEL</b>\n\nCurrent Logs Channel: <code>{cur_log}</code>\n\nSend new Channel ID, <code>@username</code>, or link (Bot must be Admin there):")
                target = _parse_channel_target(resp.text)
                entity = await bot.get_entity(target)
                chat_id = int(f"-100{entity.id}") if not str(entity.id).startswith("-100") else int(entity.id)
                set_ui_setting("log_channel_id", str(chat_id))
                await bot.send_message(chat_id, f"{P_YES} <b>Logs Channel Connected!</b>\nBot errors, new user starts, purchases, and deposits will be logged here.")
                await conv.send_message(f"{P_YES} <b>Logs Channel updated to:</b> <code>{chat_id}</code>")

            elif action_data == "cv_vouchch" and has_perm(uid, 'p_settings'):
                cur_vouch = get_vouch_channel_id()
                resp = await get_reply(f"🏆 <b>CHANGE VOUCH CHANNEL</b>\n\nCurrent Vouch Channel: <code>{cur_vouch}</code>\n\nSend new Channel ID, <code>@username</code>, or link (Bot must be Admin there):")
                target = _parse_channel_target(resp.text)
                entity = await bot.get_entity(target)
                chat_id = int(f"-100{entity.id}") if not str(entity.id).startswith("-100") else int(entity.id)
                set_ui_setting("vouch_channel_id", str(chat_id))
                await bot.send_message(chat_id, f"{P_YES} <b>Vouch Channel Connected!</b>\nSuccessful deposits and purchases will be posted here.")
                await conv.send_message(f"{P_YES} <b>Vouch Channel updated to:</b> <code>{chat_id}</code>")

            elif action_data == "cv_depgrp" and has_perm(uid, 'p_settings'):
                cur_dg = get_deposit_group_id()
                cur_url = get_deposit_group_url()
                resp = await get_reply(
                    f"🏦 <b>CHANGE DEPOSIT GROUP</b>\n\n"
                    f"Current Group ID: <code>{cur_dg}</code>\n"
                    f"Current Link: <code>{html.escape(cur_url)}</code>\n\n"
                    f"Send Deposit Group ID, <code>@username</code>, or invite link:\n"
                    f"<i>(Bot must be Admin in that group with 'Ban/Kick Users' and 'Invite Users via Link' permissions!)</i>"
                )
                raw_in = resp.text.strip()
                target = _parse_channel_target(raw_in)
                entity = await bot.get_entity(target)
                chat_id = int(f"-100{entity.id}") if not str(entity.id).startswith("-100") else int(entity.id)
                gen_url = None
                try:
                    inv = await bot(ExportChatInviteRequest(peer=entity))
                    gen_url = getattr(inv, "link", None)
                except Exception:
                    uname = getattr(entity, "username", None)
                    if uname:
                        gen_url = f"https://t.me/{uname}"
                    elif raw_in.startswith("http"):
                        gen_url = raw_in
                if not gen_url:
                    return await conv.send_message(f"{P_NO} Could not generate invite link. Make sure bot is Admin with 'Invite Users via Link' permission.")
                set_ui_setting("deposit_group_id", str(chat_id))
                set_ui_setting("deposit_group_url", gen_url)
                await conv.send_message(f"{P_YES} <b>Deposit Group Updated!</b>\n🆔 ID: <code>{chat_id}</code>\n🔗 Link: <code>{gen_url}</code>")

            elif action_data == "cv_tipbot" and has_perm(uid, 'p_settings'):
                cur_tb = get_tip_bot_username()
                resp = await get_reply(
                    f"🤖 <b>CHANGE TIP BOT</b>\n\n"
                    f"Current Tip Bot: <code>@{html.escape(cur_tb)}</code>\n\n"
                    f"Enter new Tip Bot username (e.g. <code>@cctip_bot</code>):"
                )
                new_tb = resp.text.strip().lstrip("@").lower()
                if not new_tb:
                    return await conv.send_message(f"{P_NO} Invalid username.")
                set_ui_setting("tip_bot_username", new_tb)
                await conv.send_message(f"{P_YES} <b>Tip Bot updated to:</b> <code>@{html.escape(new_tb)}</code>")

            elif action_data == "cv_tiprecv" and has_perm(uid, 'p_settings'):
                cur_tr = get_tip_receiver_username()
                resp = await get_reply(
                    f"👤 <b>CHANGE TIP RECEIVER USERNAME</b>\n\n"
                    f"Current Tip Receiver: <code>@{html.escape(cur_tr)}</code>\n\n"
                    f"Enter the Telegram username that users must tip in the Deposit Group (e.g. <code>@username</code>):"
                )
                new_tr = resp.text.strip().lstrip("@")
                if not new_tr:
                    return await conv.send_message(f"{P_NO} Invalid username.")
                set_ui_setting("tip_receiver_username", new_tr)
                await conv.send_message(f"{P_YES} <b>Tip Receiver updated to:</b> <code>@{html.escape(new_tr)}</code>")

            # -------- EXISTING ADMIN HANDLERS --------
            elif action_data == "ap_add_country" and has_perm(uid, 'p_manage_stock'):
                code = (await get_reply(f"{P_PHONE} <b>Enter Country Calling Code (without +):</b>\n<i>Example: 91</i>")).text.replace("+", "").strip()
                flag = html.escape((await get_reply(f"{P_FLAG} <b>Enter Country Flag Emoji:</b>\n<i>Example: 🇮🇳</i>")).text.strip())
                name = html.escape((await get_reply(f"{P_GLOBE} <b>Enter Country Name:</b>\n<i>Example: India</i>")).text.strip())

                cur.execute("INSERT OR REPLACE INTO custom_countries (code, name, flag) VALUES (?,?,?)", (code, name, flag))
                db.commit()
                await conv.send_message(f"{P_YES} <b>Custom Country Added Successfully!</b>\n{flag} {name} (+{code})\n\n<i>It will now automatically be recognized when adding stock!</i>")

            elif action_data == "userinfo" and has_perm(uid, 'p_stats'):
                t_uid = int((await get_reply(f"{P_ACC} <b>Enter User ID:</b>")).text)
                u_row = cur.execute("SELECT balance, total_deposited, joined_date, banned, discount FROM users WHERE user_id=?", (t_uid,)).fetchone()
                if not u_row: return await conv.send_message(f"{P_NO} User not found.")

                o_row = cur.execute("SELECT COUNT(*), SUM(price) FROM orders WHERE user_id=?", (t_uid,)).fetchone()

                bal, dep, joined, is_banned, disc = u_row
                o_count = o_row[0] if o_row else 0
                o_spent = o_row[1] if o_row and o_row[1] else 0

                msg = (f"{P_ACC} <b>USER INFO:</b> <code>{t_uid}</code>\n\n"
                       f"{P_PTS} Balance: <b>{bal} Pts</b> (${to_usd(bal):.2f})\n"
                       f"{P_CARD} Total Deposited: <b>{dep} Pts</b> (${to_usd(dep):.2f})\n"
                       f"{P_CART} Total Orders: {o_count}\n"
                       f"{P_MONEY} Total Spent: <b>{o_spent} Pts</b>\n"
                       f"{P_GIFT} Discount: {disc}%\n"
                       f"{P_CAL} Joined: {joined}\n"
                       f"{P_OFF} Banned: {'Yes' if is_banned else 'No'}")
                await conv.send_message(msg)

            elif action_data == "addadmin" and uid == ADMIN_ID:
                new_ad = int((await get_reply(f"{P_ACC} <b>Enter User ID for new Admin:</b>")).text)
                cur.execute("INSERT OR IGNORE INTO admins (user_id) VALUES (?)", (new_ad,))
                db.commit()
                await conv.send_message(f"{P_YES} Admin added!")
                class FakeEvent:
                    async def edit(self, text, buttons): await bot.send_message(chat, text, buttons=buttons)
                    async def answer(self, txt, alert): pass
                await edit_admin_menu(FakeEvent(), new_ad)

            elif action_data == "editadminreq" and uid == ADMIN_ID:
                t_id = int((await get_reply(f"{P_ACC} <b>Enter User ID to edit:</b>")).text)
                class FakeEvent:
                    async def edit(self, text, buttons): await bot.send_message(chat, text, buttons=buttons)
                    async def answer(self, txt, alert): pass
                await edit_admin_menu(FakeEvent(), t_id)

            elif action_data.startswith("msedit|") and has_perm(uid, 'p_manage_stock'):
                parts = action_data.split("|")
                action, c_name = parts[1], parts[2]

                if action == "name":
                    new_name = html.escape((await get_reply(f"{P_DOC} <b>Enter NEW Name for {c_name}:</b>")).text)
                    cur.execute("UPDATE stock SET country_name=? WHERE country_name=?", (new_name, c_name))
                    cur.execute("UPDATE auto_prices SET country=? WHERE country=?", (new_name, c_name))
                    db.commit()
                    await conv.send_message(f"{P_YES} Country '{c_name}' successfully renamed to '{new_name}'!")

                elif action == "flag":
                    new_flag = html.escape((await get_reply(f"{P_FLAG} <b>Enter NEW Flag Emoji for {c_name}:</b>")).text)
                    cur.execute("UPDATE stock SET country_icon=? WHERE country_name=?", (new_flag, c_name))
                    db.commit()
                    await conv.send_message(f"{P_YES} Flag updated to {new_flag} for '{c_name}'!")

                elif action == "cprice":
                    new_p = int((await get_reply(f"{P_PTS} <b>Enter NEW Common Price (in Points) for all {c_name} accounts:</b>")).text)
                    cur.execute("UPDATE stock SET price=? WHERE country_name=?", (new_p, c_name))
                    db.commit()
                    await conv.send_message(f"{P_YES} All existing '{c_name}' accounts updated to <b>{new_p} Pts</b>!")

                elif action == "yprice":
                    year = parts[3]
                    new_p = int((await get_reply(f"{P_PTS} <b>Enter NEW Price (in Points) for {c_name} ({year}):</b>")).text)
                    cur.execute("UPDATE stock SET price=? WHERE country_name=? AND account_year=?", (new_p, c_name, year))
                    db.commit()
                    await conv.send_message(f"{P_YES} All existing '{c_name}' ({year}) accounts updated to <b>{new_p} Pts</b>!")

            elif action_data.startswith("apset|") and has_perm(uid, 'p_manage_stock'):
                parts = action_data.split("|")
                c_name, year = parts[1], parts[2]
                new_p = int((await get_reply(f"{P_ASST} <b>Enter Auto-Price (in Points) for {c_name} ({year}):</b>\n<i>(Enter 0 to remove this auto-price)</i>")).text)
                if new_p == 0:
                    cur.execute("DELETE FROM auto_prices WHERE country=? AND year=?", (c_name, year))
                    await conv.send_message(f"{P_YES} Auto-Price for {c_name} ({year}) removed!")
                else:
                    cur.execute("INSERT OR REPLACE INTO auto_prices (country, year, price) VALUES (?,?,?)", (c_name, year, new_p))
                    await conv.send_message(f"{P_YES} Auto-Price for {c_name} ({year}) set to <b>{new_p} Pts</b>! Incoming accounts will use this price automatically.")
                db.commit()

            elif action_data == "addzip" and has_perm(uid, 'p_add_stock'):
                resp = await get_reply(f"{P_PKG} <b>Send the ZIP file containing <code>.session</code> files:</b>")
                if not resp.file or not resp.file.name.endswith('.zip'): return await conv.send_message(f"{P_NO} Invalid file.")

                await conv.send_message(f"{P_WAIT} <b>Extracting & Scanning Accounts...</b>")
                zip_path = await bot.download_media(resp, "temp_sessions.zip")
                extracted_dir = f"temp_extracted_{int(time.time())}"
                os.makedirs(extracted_dir, exist_ok=True)
                with zipfile.ZipFile(zip_path, 'r') as zip_ref: zip_ref.extractall(extracted_dir)

                groups = {}
                for file in os.listdir(extracted_dir):
                    if not file.endswith(".session"): continue
                    sess_path = os.path.join(extracted_dir, file)
                    clean_path = sess_path[:-8]
                    try:
                        client = TelegramClient(clean_path, API_ID, API_HASH)
                        await client.connect()
                        if not await client.is_user_authorized(): await client.disconnect(); continue
                        me = await client.get_me()
                        phone = getattr(me, 'phone', None)
                        if not phone: await client.disconnect(); continue

                        c_name, c_icon = get_country_info(phone)
                        pwd = await client(GetPasswordRequest())
                        has_2fa = pwd.has_password
                        year = await detect_account_year(client)
                        await client.disconnect()

                        key = (c_name, year, has_2fa)
                        if key not in groups: groups[key] = []
                        groups[key].append({"phone": phone, "path": clean_path, "c_icon": c_icon})
                    except Exception as e: logger.error(f"Scan error: {e}")

                for key in list(groups.keys()):
                    if key[0] == "Unknown":
                        sample_phone = groups[key][0]["phone"]
                        await conv.send_message(f"{P_WARN} <b>Country not recognized for +{sample_phone}!</b>")
                        new_icon = html.escape((await get_reply(f"{P_FLAG} <b>Enter Country Flag Emoji:</b>\n<i>Example: 🇮🇳</i>")).text)
                        new_name = html.escape((await get_reply(f"{P_GLOBE} <b>Enter Country Name:</b>\n<i>Example: India</i>")).text)
                        new_key = (new_name, key[1], key[2])
                        groups[new_key] = groups.pop(key)
                        for acc in groups[new_key]: acc["c_icon"] = new_icon

                success = 0
                for (c_name, year, has_2fa), accs in groups.items():
                    c_icon = accs[0]["c_icon"]
                    twofa_pass = "None"
                    if has_2fa: twofa_pass = html.escape((await get_reply(f"{P_2FA} <b>Enter 2FA Password for {len(accs)}x {c_name} accounts:</b>")).text)

                    auto_row = cur.execute("SELECT price FROM auto_prices WHERE country=? AND year=?", (c_name, str(year))).fetchone()
                    if not auto_row: auto_row = cur.execute("SELECT price FROM auto_prices WHERE country=? AND year='Common'", (c_name,)).fetchone()

                    if auto_row:
                        price = auto_row[0]
                        await conv.send_message(f"⚡ <b>Auto-Price Applied:</b> {len(accs)}x {c_name} ({year}) at <b>{price} Pts</b>.")
                    else:
                        existing_price = cur.execute("SELECT price FROM stock WHERE country_name=? LIMIT 1", (c_name,)).fetchone()
                        if existing_price:
                            price = existing_price[0]
                            await conv.send_message(f"⚡ <b>Auto-Added:</b> {len(accs)}x {c_name} at <b>{price} Pts</b> (Copied from DB).")
                        else:
                            price = int((await get_reply(f"📌 Found {len(accs)}x {c_name} ({year}).\n{P_PTS} Enter Price (Points):")).text)

                    for acc in accs:
                        perm_base = f"sessions/{acc['phone']}"
                        for ext in ['.session', '.session-wal', '.session-shm', '.session-journal']:
                            if os.path.exists(acc['path'] + ext): shutil.move(acc['path'] + ext, perm_base + ext)
                        cur.execute("INSERT OR REPLACE INTO stock (phone, session_file, country_name, country_icon, account_year, category, price, available, twofa) VALUES (?,?,?,?,?,?,?,?,?)",
                                    (acc['phone'], perm_base + ".session", c_name, c_icon, year, 'Good', price, 1, twofa_pass))
                        success += 1
                db.commit()
                os.remove(zip_path); shutil.rmtree(extracted_dir)
                await conv.send_message(f"{P_YES} <b>Bulk Interactive Upload Complete!</b>\n{P_ON} Added: {success}")

            elif action_data == "addstock" and has_perm(uid, 'p_add_stock'):
                phone = (await get_reply(f"{P_PHONE} Enter Phone (+919999...):")).text.replace(" ", "").replace("+", "")
                sp = f"sessions/{phone}"
                client = TelegramClient(sp, API_ID, API_HASH)
                await client.connect()
                sreq = await client.send_code_request(phone)

                twofa_pass = "None"
                try:
                    await client.sign_in(phone, (await get_reply(f"{P_OTP} OTP:")).text, phone_code_hash=sreq.phone_code_hash)
                except SessionPasswordNeededError:
                    twofa_pass = html.escape((await get_reply(f"{P_2FA} 2FA Pass required. Enter it now:")).text)
                    await client.sign_in(password=twofa_pass)

                c_name, c_icon = get_country_info(phone)

                if c_name == "Unknown":
                    await conv.send_message(f"{P_WARN} <b>Country not recognized for +{phone}!</b>")
                    c_icon = html.escape((await get_reply(f"{P_FLAG} <b>Enter Country Flag Emoji:</b>\n<i>Example: 🇮🇳</i>")).text)
                    c_name = html.escape((await get_reply(f"{P_GLOBE} <b>Enter Country Name:</b>\n<i>Example: India</i>")).text)

                auto_year = await detect_account_year(client)
                await client.disconnect()

                year = int((await get_reply(f"{P_CAL} Detected Year: <b>{auto_year}</b>\nReply with Year to confirm or change:")).text)
                auto_row = cur.execute("SELECT price FROM auto_prices WHERE country=? AND year=?", (c_name, str(year))).fetchone()
                if not auto_row: auto_row = cur.execute("SELECT price FROM auto_prices WHERE country=? AND year='Common'", (c_name,)).fetchone()

                if auto_row:
                    price = auto_row[0]
                    await conv.send_message(f"⚡ <b>Auto-Price Applied:</b> <b>{price} Pts</b> for {c_name} ({year})")
                else:
                    existing_price = cur.execute("SELECT price FROM stock WHERE country_name=? LIMIT 1", (c_name,)).fetchone()
                    if existing_price:
                        price = existing_price[0]
                        await conv.send_message(f"⚡ <b>Auto-detected Price:</b> <b>{price} Pts</b> for {c_name}")
                    else: price = int((await get_reply(f"{P_PTS} Price (Points):")).text)

                cur.execute("INSERT OR REPLACE INTO stock (phone, session_file, country_name, country_icon, account_year, category, price, available, twofa) VALUES (?,?,?,?,?,?,?,?,?)",
                            (phone, sp + ".session", c_name, c_icon, year, 'Good', price, 1, twofa_pass))
                db.commit()
                await conv.send_message(f"{P_YES} Added!")

            elif action_data == "supporturl" and has_perm(uid, 'p_settings'):
                url = (await get_reply("🔗 Enter new Support URL (must start with http:// or https://):")).text
                if not url.startswith("http"): url = "https://" + url.replace("@", "t.me/")
                cur.execute("UPDATE settings SET value=? WHERE key='support_url'", (url,))
                db.commit()
                await conv.send_message(f"{P_YES} Support URL updated.")

            elif action_data == "bcast" and has_perm(uid, 'p_stats'):
                txt = (await get_reply(f"{P_DOC} <b>Message (Supports HTML & tg-emoji tags):</b>")).text
                btn_name = (await get_reply(f"🔘 <b>Button Name (or 'skip'):</b>")).text
                url = (await get_reply("🔗 <b>URL:</b>")).text if btn_name.lower() != 'skip' else None
                btns = [[styled_url_btn(f"🔗 {btn_name}", url)]] if url else None
                users = cur.execute("SELECT user_id FROM users").fetchall()
                s, f = 0, 0
                await conv.send_message(f"{P_TG} Broadcasting...")
                for (u_id,) in users:
                    try:
                        await bot.send_message(int(u_id), txt, buttons=btns, parse_mode='html')
                        s += 1
                    except: f += 1
                    await asyncio.sleep(0.1)
                await conv.send_message(f"{P_YES} Done! Sent: {s} | Failed: {f}")

            elif action_data == "bal" and has_perm(uid, 'p_bal'):
                t_uid = int((await get_reply(f"{P_ACC} <b>User ID:</b>")).text)
                amt = int((await get_reply(f"{P_PTS} <b>Points Amount (Negative to deduct):</b>")).text)
                ensure_user(t_uid)
                update_balance(t_uid, amt)
                await conv.send_message(f"{P_YES} Added <b>{amt} Pts</b> to <code>{t_uid}</code>.")

            elif action_data == "discount" and has_perm(uid, 'p_settings'):
                t_uid = int((await get_reply(f"{P_ACC} <b>User ID:</b>")).text)
                pct = int((await get_reply(f"{P_GIFT} <b>Discount % (0 to remove):</b>")).text)
                cur.execute("UPDATE users SET discount=? WHERE user_id=?", (pct, t_uid))
                db.commit()
                await conv.send_message(f"{P_YES} User {t_uid} has {pct}% discount.")

            elif action_data == "refpct" and has_perm(uid, 'p_settings'):
                pct = int((await get_reply(f"{P_USERS} <b>New Referral %:</b>")).text)
                cur.execute("UPDATE settings SET value=? WHERE key='ref_percent'", (str(pct),))
                db.commit()
                await conv.send_message(f"{P_YES} Ref revenue set to {pct}%.")

            elif action_data == "ptsrate" and has_perm(uid, 'p_settings'):
                r = float((await get_reply(f"{P_PTS} <b>New Points per $1 USDT (Default 95):</b>")).text)
                if r <= 0:
                    return await conv.send_message(f"{P_NO} Rate must be greater than 0.")
                cur.execute("INSERT OR REPLACE INTO settings (key, value) VALUES ('points_rate', ?)", (str(r),))
                db.commit()
                await conv.send_message(f"{P_YES} Rate set to <b>$1 = {r} Points</b>.")

            elif action_data == "restoreusr" and has_perm(uid, 'p_settings'):
                resp = await get_reply(f"📤 <b>Send the <code>users_backup.csv</code> or backup <code>.zip</code> file:</b>")
                if not resp.file or not (resp.file.name.endswith('.csv') or resp.file.name.endswith('.zip')):
                    return await conv.send_message(f"{P_NO} Invalid file. Send a .csv or .zip backup.")

                dl_path = await bot.download_media(resp, f"temp_restore_{int(time.time())}")
                csv_path = None
                extract_dir = None
                restored_state = None

                try:
                    if dl_path.endswith(".zip"):
                        extract_dir = f"temp_restore_dir_{int(time.time())}"
                        os.makedirs(extract_dir, exist_ok=True)
                        with zipfile.ZipFile(dl_path, "r") as zf:
                            zf.extractall(extract_dir)
                        cand_csv = os.path.join(extract_dir, "users_backup.csv")
                        cand_json = os.path.join(extract_dir, "full_state_backup.json")
                        if os.path.exists(cand_csv):
                            csv_path = cand_csv
                        if os.path.exists(cand_json):
                            with open(cand_json, "r", encoding="utf-8") as jf:
                                restored_state = json.load(jf)
                        if not csv_path and not restored_state:
                            return await conv.send_message(f"{P_NO} Backup archive does not contain valid backup data.")
                    else:
                        csv_path = dl_path

                    user_count = 0
                    if csv_path and os.path.exists(csv_path):
                        with open(csv_path, "r", encoding="utf-8") as f:
                            reader = csv.reader(f)
                            header = next(reader, None)
                            for row in reader:
                                if not row or len(row) < 8:
                                    continue
                                try:
                                    cur.execute(
                                        "INSERT OR REPLACE INTO users (user_id, balance, referred_by, total_deposited, joined_date, banned, discount, terms_accepted) VALUES (?,?,?,?,?,?,?,?)",
                                        (
                                            int(row[0]),
                                            int(row[1]),
                                            int(row[2]) if str(row[2]).isdigit() else None,
                                            int(row[3]),
                                            row[4],
                                            int(row[5]),
                                            int(row[6]),
                                            int(row[7])
                                        )
                                    )
                                    user_count += 1
                                except Exception:
                                    pass

                    order_count = 0
                    if restored_state and isinstance(restored_state, dict):
                        for u in restored_state.get("users", []):
                            try:
                                cur.execute(
                                    "INSERT OR REPLACE INTO users (user_id, balance, referred_by, total_deposited, joined_date, banned, discount, terms_accepted) VALUES (?,?,?,?,?,?,?,?)",
                                    (
                                        int(u["user_id"]),
                                        int(u.get("balance", 0)),
                                        u.get("referred_by"),
                                        int(u.get("total_deposited", 0)),
                                        u.get("joined_date"),
                                        int(u.get("banned", 0)),
                                        int(u.get("discount", 0)),
                                        int(u.get("terms_accepted", 0)),
                                    )
                                )
                                if not csv_path:
                                    user_count += 1
                            except Exception:
                                pass

                        for o in restored_state.get("orders", []):
                            try:
                                cur.execute(
                                    "INSERT OR REPLACE INTO orders (id, user_id, country, year, price, phone, otp, date) VALUES (?,?,?,?,?,?,?,?)",
                                    (
                                        int(o["id"]),
                                        int(o["user_id"]),
                                        o.get("country"),
                                        int(o.get("year") or 2024),
                                        int(o.get("price", 0)),
                                        o.get("phone"),
                                        o.get("otp"),
                                        o.get("date"),
                                    )
                                )
                                order_count += 1
                            except Exception:
                                pass

                        for d in restored_state.get("deposits", []):
                            try:
                                cur.execute(
                                    "INSERT OR REPLACE INTO deposits (id, user_id, amount, method_name, status, date) VALUES (?,?,?,?,?,?)",
                                    (
                                        int(d["id"]),
                                        int(d["user_id"]),
                                        int(d.get("amount", 0)),
                                        d.get("method_name"),
                                        d.get("status", "approved"),
                                        d.get("date"),
                                    )
                                )
                            except Exception:
                                pass

                    db.commit()
                    await conv.send_message(
                        f"{P_YES} <b>Restore Complete!</b>\n"
                        f"{P_USERS} Users Restored: <b>{user_count}</b>\n"
                        f"{P_CART} Purchase History Restored: <b>{order_count}</b>"
                    )
                finally:
                    if dl_path and os.path.exists(dl_path):
                        try: os.remove(dl_path)
                        except Exception: pass
                    if extract_dir and os.path.exists(extract_dir):
                        try: shutil.rmtree(extract_dir)
                        except Exception: pass

            elif action_data == "ban" and has_perm(uid, 'p_bal'):
                t_uid = int((await get_reply(f"{P_ACC} <b>User ID:</b>")).text)
                is_ban = cur.execute("SELECT banned FROM users WHERE user_id=?", (t_uid,)).fetchone()
                if not is_ban: return await conv.send_message(f"{P_NO} User not found.")
                ns = 0 if is_ban[0] == 1 else 1
                cur.execute("UPDATE users SET banned=? WHERE user_id=?", (ns, t_uid))
                db.commit()
                await conv.send_message(f"User {t_uid} is {'Banned 🚫' if ns == 1 else 'Unbanned ✅'}.")

        except ValueError: await conv.send_message(f"{P_NO} Cancelled.")
        except Exception as e:
            await send_error_log(f"admin_actions:{action_data}", e)
            await conv.send_message(f"{P_NO} Error: {e}")

# ================= CORE EVENT ROUTERS =================
def _build_force_join_buttons(uid: int, channels: list[dict] | None = None):
    target_channels = channels if channels is not None else get_force_join_channels()
    join_style = get_button_color("Join Channel")
    verify_style = get_button_color("Verify Joined")
    btns = []
    for i, ch in enumerate(target_channels):
        ch_url = ch.get("url")
        if not ch_url:
            continue
        ch_title = ch.get('title') or f'Channel {i+1}'
        label = t(uid, "btn_join_ch", title=ch_title)
        btns.append([styled_url_btn(label, ch_url, style=join_style, icon_emoji_id=PREMIUM_EMOJI_MAP.get("MEGAPHONE"))])
    btns.append([styled_inline_btn(t(uid, "btn_verify_join"), "verify_join", style=verify_style, icon_emoji_id=PREMIUM_EMOJI_MAP.get("YES"))])
    return btns

@bot.on(events.NewMessage(pattern=r"(?i)^/start"))
async def handle_start(e):
    try:
        if not e.is_private:
            return
        uid = e.sender_id
        if not uid: return

        existing = cur.execute("SELECT user_id FROM users WHERE user_id=?", (uid,)).fetchone()
        is_new_user = existing is None
        ensure_user(uid)

        if is_user_banned(uid): return

        if not is_bot_online() and not is_admin(uid):
            return await e.respond(f"{P_OFF} <b>Bot is currently under maintenance.</b> Please try again later.")

        session_buy_state.pop(uid, None)

        ref_applied = None
        text = e.text or ''
        if len(text.split()) > 1:
            start_param = text.split()[1]
            if start_param.startswith("ref_"):
                ref = start_param.replace("ref_", "")
                if ref.isdigit() and int(ref) != uid:
                    cur.execute("UPDATE users SET referred_by=? WHERE user_id=? AND referred_by IS NULL", (int(ref), uid))
                    db.commit()
                    ref_applied = int(ref)

        if is_new_user:
            sender = await e.get_sender()
            await log_new_user_started(
                uid,
                getattr(sender, "username", None),
                getattr(sender, "first_name", None),
                ref_applied
            )

        # 1st-time language selection only (when `lang` is not yet selected)
        if not has_selected_lang(uid):
            return await send_language_menu(e, mode="first", edit_existing=False)

        missing_chs = await get_missing_force_join_channels(uid)
        if missing_chs:
            btns = _build_force_join_buttons(uid, missing_chs)
            msg = t(uid, "force_join_msg")
            return await e.respond(msg, buttons=btns)

        row = cur.execute("SELECT terms_accepted FROM users WHERE user_id=?", (uid,)).fetchone()
        terms_acc = row[0] if row else 0
        if not terms_acc:
            msg = t(uid, "terms_msg")
            btns = [
                [KeyboardButtonWebView(text=t(uid, "btn_read_terms"), url=TERMS_URL)],
                [styled_inline_btn(t(uid, "btn_accept"), "tc_accept", style="success", icon_emoji_id=PREMIUM_EMOJI_MAP.get("YES")), styled_inline_btn(t(uid, "btn_reject"), "tc_reject", style="danger", icon_emoji_id=PREMIUM_EMOJI_MAP.get("NO"))]
            ]
            return await e.respond(msg, buttons=btns)

        await send_main_menu(e, uid)
    except Exception as ex:
        await send_error_log("handle_start", ex)
        print(f"Start Error: {ex}")

async def _handle_deposit_group_message(e):
    """Handles messages inside the Deposit Group:
    1) Cancels 2-minute inactivity timer once user sends a message.
    2) Records `cc <amount> <token>` commands (including replies to recipient).
    3) Processes `@cctip_bot` tip confirmations (`airmm tip details:`):
       - Credits Points ($1 = 95 Pts) for each USDT tip >= 0.5 USDT (supports multiple tips).
       - Warns if < 0.5 USDT or wrong token, directing user to Support.
       - Sends a concise 2-line professional DM notification and kicks user after 5 seconds."""
    dep_grp_id = get_deposit_group_id()
    if not dep_grp_id or e.chat_id != dep_grp_id:
        return

    uid = e.sender_id
    raw_txt = _safe_msg_text(e)
    if not raw_txt:
        return

    sender = await e.get_sender()
    sender_uname = (getattr(sender, "username", None) or "").lower()
    tip_bot_uname = get_tip_bot_username()
    is_from_tip_bot = bool(sender_uname and sender_uname == tip_bot_uname)

    if not is_from_tip_bot:
        if uid:
            watcher = deposit_group_watchers.get(uid)
            if watcher:
                watcher["has_messaged"] = True
                t = watcher.get("task")
                if t:
                    t.cancel()

        # Detect `cc <amount> <token>` command (with or without replying to receiver)
        cc_match = re.search(r"(?i)^\s*cc\s+([0-9]+(?:\.[0-9]+)?)\s+([A-Za-z0-9_]+)", raw_txt)
        if cc_match and uid:
            try:
                cmd_amt = float(cc_match.group(1))
                cmd_token = cc_match.group(2).strip().upper()
                msg_id = getattr(e, "id", None)
                recent_cc_commands.append({
                    "ts": time.time(),
                    "uid": uid,
                    "amt": cmd_amt,
                    "token": cmd_token,
                    "msg_id": msg_id,
                    "consumed": False
                })
                if uid in deposit_group_watchers:
                    deposit_group_watchers[uid]["pending_tips"] = deposit_group_watchers[uid].get("pending_tips", 0) + 1
                if len(recent_cc_commands) > 50:
                    del recent_cc_commands[:-50]
            except Exception:
                pass
        return

    # Message from @cctip_bot
    if "tip details" not in raw_txt.lower():
        return

    # Identify depositor via reply_to_msg_id or most recent unconsumed `cc` command
    depositor_uid = None
    matched_entry = None
    try:
        reply_msg = await e.get_reply_message()
        if reply_msg and reply_msg.sender_id:
            depositor_uid = reply_msg.sender_id
            for entry in reversed(recent_cc_commands):
                if entry.get("msg_id") == reply_msg.id:
                    matched_entry = entry
                    break
    except Exception:
        pass

    # Check if tip is USDT or another token (e.g., TRX, BTC, TON)
    usdt_match = re.search(r"(?i)\bUSDT\s*\+\s*([0-9]+(?:\.[0-9]+)?)(?:\s+@?([A-Za-z0-9_]+))?", raw_txt)
    other_token_match = re.search(r"(?i)\b([A-Z]{2,10})\s*\+\s*([0-9]+(?:\.[0-9]+)?)(?:\s+@?([A-Za-z0-9_]+))?", raw_txt)

    if not depositor_uid:
        now = time.time()
        target_amt = None
        if usdt_match:
            target_amt = float(usdt_match.group(1))
        elif other_token_match:
            target_amt = float(other_token_match.group(2))

        for entry in reversed(recent_cc_commands):
            if entry.get("consumed") or (now - entry["ts"]) > 180:
                continue
            if target_amt is None or abs(entry["amt"] - target_amt) < 1e-6:
                depositor_uid = entry["uid"]
                matched_entry = entry
                break

    if matched_entry:
        matched_entry["consumed"] = True

    if depositor_uid and depositor_uid in deposit_group_watchers:
        cur_p = deposit_group_watchers[depositor_uid].get("pending_tips", 1)
        deposit_group_watchers[depositor_uid]["pending_tips"] = max(0, cur_p - 1)

    if not usdt_match:
        # Wrong token tipped
        warn_token_msg = (
            f"{P_WARN} <a href='tg://user?id={depositor_uid}'>Member</a>, unsupported token detected in your tip.\n"
            f"Only <b>USDT</b> deposits are supported automatically—please contact <b>Support</b> for assistance."
            if depositor_uid else
            f"{P_WARN} Unsupported token tip detected. Only <b>USDT</b> deposits are supported—please contact <b>Support</b> for assistance."
        )
        await bot.send_message(dep_grp_id, warn_token_msg)
        if depositor_uid:
            asyncio.create_task(_delayed_kick_after_deposit(dep_grp_id, depositor_uid, delay=5))
        return

    usdt_amt = float(usdt_match.group(1))
    recipient_uname = (usdt_match.group(2) or "").lstrip("@").lower()
    expected_recv = get_tip_receiver_username().lstrip("@").lower()

    if recipient_uname and expected_recv and expected_recv != "support":
        if recipient_uname != expected_recv:
            return

    if not depositor_uid:
        logger.warning(f"USDT tip ({usdt_amt}) confirmed but depositor could not be identified.")
        return

    if usdt_amt < MIN_DEPOSIT_USDT:
        min_warn = (
            f"{P_WARN} <a href='tg://user?id={depositor_uid}'>Member</a>, your deposit of <b>{usdt_amt} USDT</b> is below the <b>0.5 USDT</b> minimum.\n"
            f"Deposits under <b>0.5 USDT</b> are not counted—please contact <b>Support</b> if you have already sent funds."
        )
        await bot.send_message(dep_grp_id, min_warn)
        asyncio.create_task(_delayed_kick_after_deposit(dep_grp_id, depositor_uid, delay=5))
        return

    rate = get_points_rate()
    rate_disp = int(rate) if rate.is_integer() else rate
    pts_added = int(round(usdt_amt * rate))
    ensure_user(depositor_uid)

    async with get_user_lock(depositor_uid):
        prev_row = cur.execute("SELECT balance FROM users WHERE user_id=?", (depositor_uid,)).fetchone()
        prev_bal = prev_row[0] if prev_row else 0
        new_bal = prev_bal + pts_added
        update_balance(depositor_uid, pts_added)
        cur.execute("UPDATE users SET total_deposited = total_deposited + ? WHERE user_id=?", (pts_added, depositor_uid))
        cur.execute(
            "INSERT INTO deposits (user_id, amount, method_name, status) VALUES (?,?,?,?)",
            (depositor_uid, pts_added, f"USDT Tip (${usdt_amt})", "approved")
        )
        db.commit()

    await process_referral_bonus(depositor_uid, pts_added)
    await log_primary_deposit(depositor_uid, pts_added, usdt_amt, f"USDT Tip (@{tip_bot_uname})")

    # Strictly 2-line professional DM notification
    dm_notice = (
        f"{P_YES} Deposit Credited — <b>{pts_added} Points</b> (${usdt_amt:.2f} USDT) added to your account.\n"
        f"{P_PTS} Updated Balance: <b>{new_bal} Points</b> | Rate: $1 = {rate_disp} Points."
    )
    try:
        await bot.send_message(depositor_uid, dm_notice)
    except Exception:
        pass

    grp_confirm = (
        f"{P_YES} <a href='tg://user?id={depositor_uid}'>Deposit Confirmed</a> — <b>+{pts_added} Points</b> (${usdt_amt:.2f} USDT) credited.\n"
        f"<i>Removing you from the deposit group in 5 seconds...</i>"
    )
    await bot.send_message(dep_grp_id, grp_confirm)
    asyncio.create_task(_delayed_kick_after_deposit(dep_grp_id, depositor_uid, delay=5))

@bot.on(events.NewMessage())
async def handle_all_messages(e):
    try:
        # Only process group updates for the configured Deposit Group; never send messages to other groups
        if not e.is_private:
            dep_grp_id = get_deposit_group_id()
            if dep_grp_id and e.chat_id == dep_grp_id:
                await _handle_deposit_group_message(e)
            return

        uid = e.sender_id
        if not uid: return
        if _safe_msg_text(e).startswith('/'): return
        if not is_bot_online() and not is_admin(uid):
            return await e.respond(f"{P_OFF} <b>Bot is currently under maintenance.</b> Please try again later.")

        ensure_user(uid)
        if is_user_banned(uid): return

        text = _safe_msg_text(e)
        if not text: return

        # Enforce force-join even if user already started the bot earlier
        missing_chs = await get_missing_force_join_channels(uid)
        if missing_chs:
            return await e.respond(t(uid, "force_join_msg"), buttons=_build_force_join_buttons(uid, missing_chs))

        if "Buy Account" in text or "Buy Sessions" in text or "Deposit" in text or "My Profile" in text or "My Stats" in text or "Support" in text or "Admin Panel" in text:
            session_buy_state.pop(uid, None)

        if uid in session_buy_state:
            state = session_buy_state[uid]
            try:
                qty = int(re.sub(r'[^\d]', '', text))
                if qty < 1: raise ValueError
                if qty > state['stock']: return await e.respond(f"{P_WARN} <b>Not enough stock!</b> Max is {state['stock']}.")

                disc_row = cur.execute("SELECT discount FROM users WHERE user_id=?", (uid,)).fetchone()
                discount = disc_row[0] if disc_row else 0
                total_cost = qty * state['price']
                if discount > 0: total_cost = int(total_cost * (100 - discount) / 100)

                bal_row = cur.execute("SELECT balance FROM users WHERE user_id=?", (uid,)).fetchone()
                user_bal = bal_row[0] if bal_row else 0
                if user_bal < total_cost:
                    return await e.respond(f"{P_NO} <b>Insufficient Balance!</b>\nYou need <b>{total_cost} Pts</b> to buy {qty} sessions.")

                session_buy_state.pop(uid)
                await process_bulk_sessions(e, uid, qty, state, total_cost)
                return
            except ValueError:
                return await e.respond(f"{P_NO} Please enter a valid number.")

        matched_btn = _resolve_canonical_kb_name(text)
        if matched_btn == "Buy Account": await show_countries(e, 'single', 1)
        elif matched_btn == "Buy Sessions": await show_countries(e, 'bulk', 1)
        elif matched_btn == "Deposit": await deposit_menu(e)
        elif matched_btn == "My Profile": await profile_handler(e)
        elif matched_btn == "My Stats": await stats_handler(e)
        elif matched_btn == "Language": await send_language_menu(e, mode="switch", edit_existing=False)
        elif matched_btn == "Support":
            fjoin_chs = get_force_join_channels()
            ch_url = fjoin_chs[0]["url"] if fjoin_chs else JOIN_URLS[0]
            await e.reply(
                t(uid, "support_msg"),
                buttons=[
                    [styled_url_btn(t(uid, "btn_support_url"), get_support_url())],
                    [KeyboardButtonWebView(text=t(uid, "btn_terms_url"), url=TERMS_URL)],
                    [styled_url_btn(t(uid, "btn_channel_url"), ch_url)]
                ]
            )
        elif matched_btn == "Admin Panel":
            if is_admin(uid): await admin_panel_handler(e)

    except Exception as ex:
        await send_error_log("handle_all_messages", ex)
        print(f"Message Error: {ex}")

@bot.on(events.CallbackQuery)
async def handle_callback_query(e):
    try:
        uid = e.sender_id
        if not is_bot_online() and not is_admin(uid):
            return await e.answer("⚙️ Bot is under maintenance.", alert=True)

        ensure_user(uid)
        now = time.time()
        if uid in user_spam_cooldown and now - user_spam_cooldown[uid] < 0.5:
            return await e.answer("⚠️ Please slow down! Don't spam buttons.", alert=True)
        user_spam_cooldown[uid] = now

        if is_user_banned(uid): return await e.answer("🚫 BANNED", alert=True)
        data = e.data.decode()

        if data != "verify_join" and not data.startswith("set_lang|") and not data.startswith("open_lang_menu|"):
            missing_chs = await get_missing_force_join_channels(uid)
            if missing_chs:
                await bot.send_message(uid, t(uid, "force_join_msg"), buttons=_build_force_join_buttons(uid, missing_chs))
                return await e.answer(t(uid, "must_join_alert"), alert=True)

        if data.startswith("open_lang_menu|"):
            mode = data.split("|", 1)[1]
            return await send_language_menu(e, mode=mode, edit_existing=True)

        elif data.startswith("set_lang|"):
            parts = data.split("|")
            mode = parts[1] if len(parts) > 1 else "switch"
            chosen = parts[2] if len(parts) > 2 else "en"
            set_user_lang(uid, chosen)
            if mode == "first":
                await e.answer(t(uid, "lang_set_continue"), alert=False)
                missing_chs = await get_missing_force_join_channels(uid)
                if missing_chs:
                    btns = _build_force_join_buttons(uid, missing_chs)
                    try:
                        await e.edit(t(uid, "force_join_msg"), buttons=btns)
                    except Exception:
                        try: await e.delete()
                        except Exception: pass
                        await bot.send_message(uid, t(uid, "force_join_msg"), buttons=btns)
                    return
                row = cur.execute("SELECT terms_accepted FROM users WHERE user_id=?", (uid,)).fetchone()
                terms_acc = row[0] if row else 0
                if not terms_acc:
                    btns = [
                        [KeyboardButtonWebView(text=t(uid, "btn_read_terms"), url=TERMS_URL)],
                        [styled_inline_btn(t(uid, "btn_accept"), "tc_accept", style="success", icon_emoji_id=PREMIUM_EMOJI_MAP.get("YES")), styled_inline_btn(t(uid, "btn_reject"), "tc_reject", style="danger", icon_emoji_id=PREMIUM_EMOJI_MAP.get("NO"))]
                    ]
                    try:
                        await e.edit(t(uid, "terms_msg"), buttons=btns)
                    except Exception:
                        try: await e.delete()
                        except Exception: pass
                        await bot.send_message(uid, t(uid, "terms_msg"), buttons=btns)
                    return
                await send_main_menu(e, uid)
            else:
                await e.answer(t(uid, "lang_updated"), alert=False)
                try:
                    await e.delete()
                except Exception:
                    pass
                await bot.send_message(uid, t(uid, "lang_updated"), buttons=get_persistent_menu(uid))
            return

        if data == "verify_join":
            missing_chs = await get_missing_force_join_channels(uid)
            if missing_chs:
                try:
                    await e.edit(t(uid, "force_join_msg"), buttons=_build_force_join_buttons(uid, missing_chs))
                except MessageNotModifiedError:
                    pass
                return await e.answer(t(uid, "must_join_alert"), alert=True)
            row = cur.execute("SELECT terms_accepted FROM users WHERE user_id=?", (uid,)).fetchone()
            terms = row[0] if row else 0
            if not terms:
                msg = t(uid, "terms_msg")
                btns = [[KeyboardButtonWebView(text=t(uid, "btn_read_terms"), url=TERMS_URL)], [styled_inline_btn(t(uid, "btn_accept"), "tc_accept", style="success", icon_emoji_id=PREMIUM_EMOJI_MAP.get("YES")), styled_inline_btn(t(uid, "btn_reject"), "tc_reject", style="danger", icon_emoji_id=PREMIUM_EMOJI_MAP.get("NO"))]]
                try: await e.edit(msg, buttons=btns)
                except MessageNotModifiedError: pass
                return
            await send_main_menu(e, uid)

        elif data == "tc_accept":
            cur.execute("UPDATE users SET terms_accepted=1 WHERE user_id=?", (uid,))
            db.commit()
            await e.answer(t(uid, "terms_accepted_alert"), alert=True)
            await send_main_menu(e, uid)

        elif data == "tc_reject":
            try: await e.edit(t(uid, "terms_rejected_msg"))
            except MessageNotModifiedError: pass

        elif data == "cancel_action":
            session_buy_state.pop(uid, None)
            try: await e.edit(t(uid, "cancelled_msg"))
            except MessageNotModifiedError: pass

        elif data.startswith("pg_c|"):
            p = data.split("|")
            await show_countries(e, p[1], int(p[2]))

        elif data.startswith("bc|"):
            p = data.split("|")
            await show_years(e, p[1], p[2])

        elif data.startswith("by|"):
            p = data.split("|")
            if p[1] == 'single': await confirm_purchase(e, p[2], p[3], p[4])
            else: await init_session_purchase(e, p[2], p[3], p[4])

        elif data.startswith("buy_cf|"):
            p = data.split("|")
            await process_purchase(e, p[1], p[2], p[3])

        elif data.startswith("get_otp_again|"):
            phone = data.split("|")[1]
            if phone not in active_orders:
                return await e.answer("⚠️ Session already logged out or expired.", alert=True)

            order = active_orders[phone]
            client = order['client']
            start_time = order['start_time']

            await e.answer("🔄 Fetching latest OTP...", alert=False)
            try:
                msgs = await client.get_messages(777000, limit=5)
                latest_code = None
                for m in msgs:
                    if m.date.timestamp() > start_time - 10:
                        if m.message and re.search(OTP_REGEX, m.message) and "Login detected" not in m.message:
                            latest_code = re.search(OTP_REGEX, m.message).group()
                            break

                if latest_code:
                    twofa_text = f"{P_2FA} <b>2FA:</b> <code>{order['twofa']}</code>" if order['twofa'] != "None" else f"🔓 <b>2FA:</b> <code>Disabled (No Password)</code>"
                    msg = (f"{P_YES} <b>Latest OTP Fetched!</b>\n\n"
                           f"{P_PHONE} <b>Phone:</b> <code>{phone}</code>\n"
                           f"{P_FLAG} <b>Country:</b> {order['c_icon']} {order['country']}\n"
                           f"{P_OTP} <b>OTP:</b> <code>{latest_code}</code>\n"
                           f"{twofa_text}")
                    try: await e.edit(msg, buttons=[[styled_inline_btn("🔄 Get OTP Again", f"get_otp_again|{phone}", style="primary", icon_emoji_id=PREMIUM_EMOJI_MAP.get("OTP"))], [styled_inline_btn("🚪 Finish & Logout", f"logout_bot|{phone}", style="danger", icon_emoji_id=PREMIUM_EMOJI_MAP.get("OFF"))]])
                    except MessageNotModifiedError: pass
                else:
                    await e.answer("⏳ No new OTP found yet. Try again in a few seconds.", alert=True)
            except Exception as ex:
                await e.answer("❌ Error fetching OTP.", alert=True)

        elif data.startswith("logout_bot|"):
            phone = data.split("|")[1]
            if phone in active_orders:
                order = active_orders.pop(phone)
                try: await order['client'].log_out()
                except: pass
                try: await order['client'].disconnect()
                except: pass
                delete_session_files(order['sess'])
                await e.edit(f"{P_YES} <b>Session Finished & Logged out successfully.</b>")
            else:
                await e.answer("⚠️ No active order found or already logged out.", alert=True)

        elif data.startswith("page_purchases_"): await send_purchase_page(e, uid, int(data.split("_")[2]))
        elif data == "back_to_stats": await stats_handler(e, is_callback=True)
        elif data == "view_referrals": await view_referrals(e)

        elif data.startswith("adm_") and is_admin(uid): await admin_actions(e)

    except Exception as ex:
        await send_error_log("handle_callback_query", ex)
        print(f"Callback Error: {ex}")

import hashlib
import signal

_shutdown_event: asyncio.Event | None = None
_last_backup_hash: str | None = get_ui_setting("last_backup_hash")

def _compute_db_state_fingerprint() -> str:
    """Computes a deterministic hash of users (points, referrals, deposits, status) and orders/deposits history."""
    users_rows = cur.execute(
        "SELECT user_id, balance, referred_by, total_deposited, joined_date, banned, discount, terms_accepted "
        "FROM users ORDER BY user_id ASC"
    ).fetchall()
    orders_rows = cur.execute(
        "SELECT id, user_id, country, year, price, phone, otp, date FROM orders ORDER BY id ASC"
    ).fetchall()
    deposits_rows = cur.execute(
        "SELECT id, user_id, amount, method_name, status, date FROM deposits ORDER BY id ASC"
    ).fetchall()
    payload = json.dumps(
        {"users": users_rows, "orders": orders_rows, "deposits": deposits_rows},
        ensure_ascii=False,
        default=str
    )
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()

def _create_backup_zip(zip_path: str) -> tuple[int, int]:
    """Creates a backup ZIP containing `users_backup.csv` (compatible with restoreusr)
    and `full_state_backup.json` (users + buy history + deposits)."""
    users_rows = cur.execute(
        "SELECT user_id, balance, referred_by, total_deposited, joined_date, banned, discount, terms_accepted "
        "FROM users ORDER BY user_id ASC"
    ).fetchall()
    orders_cols = ["id", "user_id", "country", "year", "price", "phone", "otp", "date"]
    orders_rows = cur.execute(
        "SELECT id, user_id, country, year, price, phone, otp, date FROM orders ORDER BY id ASC"
    ).fetchall()
    dep_cols = ["id", "user_id", "amount", "method_name", "status", "date"]
    deposits_rows = cur.execute(
        "SELECT id, user_id, amount, method_name, status, date FROM deposits ORDER BY id ASC"
    ).fetchall()

    csv_name = "users_backup.csv"
    with open(csv_name, "w", newline="", encoding="utf-8") as cf:
        w = csv.writer(cf)
        w.writerow(["user_id", "balance", "referred_by", "total_deposited", "joined_date", "banned", "discount", "terms_accepted"])
        w.writerows(users_rows)

    state_obj = {
        "exported_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        "users": [
            {
                "user_id": r[0], "balance": r[1], "referred_by": r[2],
                "total_deposited": r[3], "joined_date": r[4], "banned": r[5],
                "discount": r[6], "terms_accepted": r[7]
            }
            for r in users_rows
        ],
        "orders": [dict(zip(orders_cols, r)) for r in orders_rows],
        "deposits": [dict(zip(dep_cols, r)) for r in deposits_rows],
    }

    try:
        with zipfile.ZipFile(zip_path, "w", compression=zipfile.ZIP_DEFLATED) as zf:
            zf.write(csv_name, "users_backup.csv")
            zf.writestr("full_state_backup.json", json.dumps(state_obj, indent=2, ensure_ascii=False, default=str))
    finally:
        if os.path.exists(csv_name):
            try: os.remove(csv_name)
            except Exception: pass

    return len(users_rows), len(orders_rows)

async def _auto_db_backup_worker():
    """Every 10 minutes (600s), checks if users/points/orders/deposits changed; if so, sends backup to Logs Channel."""
    global _last_backup_hash
    while _shutdown_event and not _shutdown_event.is_set():
        try:
            await asyncio.sleep(600)
        except asyncio.CancelledError:
            break
        if _shutdown_event.is_set():
            break

        try:
            log_ch = get_log_channel_id()
            if not log_ch:
                continue
            curr_hash = _compute_db_state_fingerprint()
            if curr_hash == _last_backup_hash:
                continue

            zip_path = f"auto_users_backup_{int(time.time())}.zip"
            u_cnt, o_cnt = _create_backup_zip(zip_path)
            try:
                caption = (
                    f"{P_DOC} <b>AUTO DB BACKUP (10-MIN SYNC)</b>\n\n"
                    f"{P_USERS} <b>Total Users:</b> {u_cnt}\n"
                    f"{P_CART} <b>Purchase History Records:</b> {o_cnt}\n"
                    f"{P_TIME} <b>Time:</b> {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n"
                    f"<i>Compatible with Admin Panel → Restore Users</i>"
                )
                await bot.send_file(log_ch, zip_path, caption=caption)
                _last_backup_hash = curr_hash
                set_ui_setting("last_backup_hash", curr_hash)
            finally:
                if os.path.exists(zip_path):
                    try: os.remove(zip_path)
                    except Exception: pass
        except asyncio.CancelledError:
            break
        except Exception as e:
            logger.error(f"Auto backup error: {e}")

async def _cleanup_and_shutdown():
    """Cleanly cancels tasks, closes session clients, checkpoints & closes SQLite DB, and disconnects bot."""
    for uid, w in list(deposit_group_watchers.items()):
        t = w.get("task")
        if t and not t.done():
            t.cancel()
    deposit_group_watchers.clear()

    for phone, order in list(active_orders.items()):
        cli = order.get("client")
        if cli:
            try: await cli.disconnect()
            except Exception: pass
    active_orders.clear()

    try:
        if bot.is_connected():
            await bot.disconnect()
    except Exception:
        pass

    try:
        db.commit()
        cur.execute("PRAGMA wal_checkpoint(TRUNCATE);")
        db.commit()
        db.close()
    except Exception:
        pass

async def main():
    global _shutdown_event
    _shutdown_event = asyncio.Event()
    backup_task = asyncio.create_task(_auto_db_backup_worker())
    print("✅ ULTIMATE ADVANCED POINTS & TIP BOT STARTED SUCCESSFULLY")
    try:
        await bot.run_until_disconnected()
    except asyncio.CancelledError:
        pass
    finally:
        if _shutdown_event:
            _shutdown_event.set()
        if not backup_task.done():
            backup_task.cancel()
            try:
                await backup_task
            except asyncio.CancelledError:
                pass
        await _cleanup_and_shutdown()

if __name__ == '__main__':
    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    _sig_triggered = False

    def _request_stop():
        global _sig_triggered
        if _sig_triggered:
            return
        _sig_triggered = True
        if _shutdown_event and not _shutdown_event.is_set():
            _shutdown_event.set()
        for t in asyncio.all_tasks(loop):
            if not t.done():
                t.cancel()
        try:
            if bot.is_connected():
                loop.create_task(bot.disconnect())
        except Exception:
            pass

    def _handle_sig(signum, frame):
        try:
            if not loop.is_closed():
                loop.call_soon_threadsafe(_request_stop)
        except Exception:
            pass
        raise KeyboardInterrupt()

    for sig in (signal.SIGINT, signal.SIGTERM):
        try:
            signal.signal(sig, _handle_sig)
        except Exception:
            pass

    try:
        bot.start(bot_token=BOT_TOKEN)
        loop.run_until_complete(main())
    except (KeyboardInterrupt, SystemExit, asyncio.CancelledError):
        pass
    finally:
        try:
            if not loop.is_closed():
                loop.run_until_complete(_cleanup_and_shutdown())
        except Exception:
            pass
        try:
            pending = [t for t in asyncio.all_tasks(loop) if not t.done()]
            for t in pending:
                t.cancel()
            if pending:
                loop.run_until_complete(asyncio.gather(*pending, return_exceptions=True))
        except Exception:
            pass
        try:
            if not loop.is_closed():
                loop.stop()
                loop.close()
        except Exception:
            pass
        print("\n🛑 Bot stopped cleanly.")


