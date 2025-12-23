# -*- coding: utf-8 -*-
"""📚 Scientific Article Analyzer by DOI with smart caching and Excel export
Adapted for Streamlit
"""

# ============================================================================
# 📦 IMPORTS AND SETUP
# ============================================================================

import streamlit as st
import requests
import json
import re
import time
import pickle
import hashlib
import os
import pandas as pd
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Any, Tuple, Set, Union
from collections import defaultdict, Counter, OrderedDict
from concurrent.futures import ThreadPoolExecutor, as_completed
from tqdm import tqdm
import warnings
warnings.filterwarnings('ignore')
import threading
from queue import Queue
import math
from collections import deque
import networkx as nx
from sklearn.ensemble import IsolationForest
from sklearn.preprocessing import StandardScaler
import numpy as np
import tempfile
import base64
from io import BytesIO
import joblib
from fuzzywuzzy import fuzz
import concurrent.futures

# Streamlit page configuration
st.set_page_config(
    page_title="📚 Scientific Article Analyzer by DOI",
    page_icon="📊",
    layout="wide",
    initial_sidebar_state="expanded"
)

# ============================================================================
# ⚙️ CONFIGURATION
# ============================================================================

class Config:
    CROSSREF_URL = "https://api.crossref.org/works/"
    OPENALEX_URL = "https://api.openalex.org/works/https://doi.org/"
    OPENALEX_WORKS_URL = "https://api.openalex.org/works"
    ORCID_API_URL = "https://pub.orcid.org/v3.0/search/"
    ROR_API_URL = "https://api.ror.org/organizations"

    REQUEST_TIMEOUT = 10
    MAX_RETRIES = 2
    MAX_DELAY = 1.0
    MIN_DELAY = 0.1
    INITIAL_DELAY = 0.2

    # For Streamlit use temporary directory in session
    CACHE_DIR = tempfile.mkdtemp(prefix="article_analyzer_cache_")
    TTL_HOURS = 24
    MAX_CACHE_SIZE_MB = 50

    MIN_WORKERS = 1
    MAX_WORKERS = 10
    DEFAULT_WORKERS = 4

    BATCH_SIZE = 50

    TOP_PERCENTILE_FOR_DEEP_ANALYSIS = 10
    MIN_CITATIONS_FOR_DEEP_ANALYSIS = 10

    COUNTRY_CODES = {
        'USA': 'US', 'United States': 'US', 'US': 'US',
        'United Kingdom': 'GB', 'UK': 'GB', 'Great Britain': 'GB',
        'Germany': 'DE', 'Deutschland': 'DE',
        'France': 'FR', 'France': 'FR',
        'China': 'CN', 'People\'s Republic of China': 'CN', 'PR China': 'CN',
        'Japan': 'JP', 'Japan': 'JP',
        'Canada': 'CA', 'Canada': 'CA',
        'Australia': 'AU', 'Australia': 'AU',
        'Italy': 'IT', 'Italia': 'IT',
        'Spain': 'ES', 'España': 'ES',
        'Russia': 'RU', 'Russian Federation': 'RU', 'Россия': 'RU', 'Russian': 'RU',
        'India': 'IN', 'India': 'IN',
        'Brazil': 'BR', 'Brasil': 'BR',
        'South Korea': 'KR', 'Korea, Republic of': 'KR', 'Korea': 'KR',
        'Netherlands': 'NL', 'The Netherlands': 'NL',
        'Switzerland': 'CH', 'Switzerland': 'CH',
        'Sweden': 'SE', 'Sweden': 'SE',
        'Norway': 'NO', 'Norway': 'NO',
        'Denmark': 'DK', 'Denmark': 'DK',
        'Finland': 'FI', 'Finland': 'FI',
        'Austria': 'AT', 'Austria': 'AT',
        'Belgium': 'BE', 'Belgium': 'BE',
        'Poland': 'PL', 'Poland': 'PL',
        'Portugal': 'PT', 'Portugal': 'PT',
        'Greece': 'GR', 'Greece': 'GR',
        'Turkey': 'TR', 'Türkiye': 'TR',
        'Israel': 'IL', 'Israel': 'IL',
        'Singapore': 'SG', 'Singapore': 'SG',
        'Taiwan': 'TW', 'Taiwan, Province of China': 'TW',
        'Hong Kong': 'HK', 'Hong Kong SAR': 'HK',
        'Mexico': 'MX', 'Mexico': 'MX',
        'Argentina': 'AR', 'Argentina': 'AR',
        'Chile': 'CL', 'Chile': 'CL',
        'Colombia': 'CO', 'Colombia': 'CO',
        'Ukraine': 'UA', 'Ukraine': 'UA',
        'Czech Republic': 'CZ', 'Czechia': 'CZ',
        'Hungary': 'HU', 'Hungary': 'HU',
        'Romania': 'RO', 'Romania': 'RO',
        'Bulgaria': 'BG', 'Bulgaria': 'BG',
        'Serbia': 'RS', 'Serbia': 'RS',
        'Croatia': 'HR', 'Croatia': 'HR',
        'Slovakia': 'SK', 'Slovakia': 'SK',
        'Slovenia': 'SI', 'Slovenia': 'SI',
        'Lithuania': 'LT', 'Lithuania': 'LT',
        'Latvia': 'LV', 'Latvia': 'LV',
        'Estonia': 'EE', 'Estonia': 'EE',
        'Ireland': 'IE', 'Ireland': 'IE',
        'New Zealand': 'NZ', 'New Zealand': 'NZ',
        'South Africa': 'ZA', 'South Africa': 'ZA',
        'Egypt': 'EG', 'Egypt': 'EG',
        'Saudi Arabia': 'SA', 'Saudi Arabia': 'SA',
        'United Arab Emirates': 'AE', 'UAE': 'AE',
        'Qatar': 'QA', 'Qatar': 'QA',
        'Iran': 'IR', 'Iran, Islamic Republic of': 'IR',
        'Pakistan': 'PK', 'Pakistan': 'PK',
        'Bangladesh': 'BD', 'Bangladesh': 'BD',
        'Vietnam': 'VN', 'Viet Nam': 'VN',
        'Thailand': 'TH', 'Thailand': 'TH',
        'Malaysia': 'MY', 'Malaysia': 'MY',
        'Indonesia': 'ID', 'Indonesia': 'ID',
        'Philippines': 'PH', 'Philippines': 'PH',
        'Kazakhstan': 'KZ', 'Kazakhstan': 'KZ',
        'Belarus': 'BY', 'Belarus': 'BY',
        'Uzbekistan': 'UZ', 'Uzbekistan': 'UZ',
        'Azerbaijan': 'AZ', 'Azerbaijan': 'AZ',
        'Georgia': 'GE', 'Georgia': 'GE',
        'Armenia': 'AM', 'Armenia': 'AM',
        'Moldova': 'MD', 'Moldova': 'MD',
        'Kyrgyzstan': 'KG', 'Kyrgyzstan': 'KG',
        'Tajikistan': 'TJ', 'Tajikistan': 'TJ',
        'Turkmenistan': 'TM', 'Turkmenistan': 'TM',
        'Mongolia': 'MN', 'Mongolia': 'MN',
    }

# ============================================================================
# 🗂️ SMART CACHE MANAGER
# ============================================================================

class SmartCacheManager:
    def __init__(self, cache_dir: str = Config.CACHE_DIR, ttl_hours: int = Config.TTL_HOURS):
        self.cache_dir = cache_dir
        self.ttl_seconds = ttl_hours * 3600

        self.stats = {
            'hits': 0,
            'misses': 0,
            'expired': 0,
            'evictions': 0,
            'total_size_mb': 0,
            'memory_hits': 0,
            'file_hits': 0,
            'api_calls_saved': 0
        }

        self.memory_cache = OrderedDict()
        self.max_memory_items = 5000

        self.failed_cache = {}
        self.failed_cache_ttl = 3600

        self.popular_cache = {}

        self.ror_cache = {
            'analyzed': {},
            'ref': {},
            'citing': {},
            'summary': {}
        }

        self.insights_cache = {
            'geo_bubbles': {},
            'temporal_patterns': {},
            'hyper_citation': {},
            'citation_cascades': {},
            'mutual_citations': {}
        }

        # New cache for processing progress
        self.progress_cache = {
            'last_processed': {},
            'remaining_dois': {},
            'current_stage': {}
        }

        if not os.path.exists(cache_dir):
            os.makedirs(cache_dir, exist_ok=True)

        self._clean_expired_cache()

        self._load_popular_dois()
        self._load_progress_cache()

    def _get_cache_key(self, source: str, identifier: str) -> str:
        key_str = f"v3:{source}:{identifier}"
        return hashlib.sha256(key_str.encode()).hexdigest()[:32]

    def _get_cache_path(self, key: str) -> str:
        return os.path.join(self.cache_dir, f"{key}.pkl")

    def _get_cache_metadata_path(self, key: str) -> str:
        return os.path.join(self.cache_dir, f"{key}_meta.json")

    def cache_function_result(self, func_name: str, func_args: tuple, result: Any, 
                         ttl_seconds: int = 3600):
        """Кэширует результат выполнения функции"""
        args_hash = hashlib.md5(str(func_args).encode()).hexdigest()
        cache_key = f"func:{func_name}:{args_hash}"
        
        cache_entry = {
            'result': result,
            'timestamp': time.time(),
            'ttl': ttl_seconds,
            'func_name': func_name
        }
        
        # Сохраняем в памяти
        self.function_cache[cache_key] = cache_entry
        
        # Также сохраняем на диск для устойчивости
        self._save_to_disk_cache(cache_key, cache_entry, category="function_results")
    
    def get_cached_function_result(self, func_name: str, func_args: tuple):
        """Получает кэшированный результат функции"""
        args_hash = hashlib.md5(str(func_args).encode()).hexdigest()
        cache_key = f"func:{func_name}:{args_hash}"
        
        # Пробуем получить из memory cache
        if cache_key in self.function_cache:
            entry = self.function_cache[cache_key]
            if time.time() - entry['timestamp'] < entry['ttl']:
                return entry['result']
        
        # Пробуем получить из disk cache
        disk_entry = self._load_from_disk_cache(cache_key, "function_results")
        if disk_entry and time.time() - disk_entry['timestamp'] < disk_entry['ttl']:
            # Восстанавливаем в memory cache
            self.function_cache[cache_key] = disk_entry
            return disk_entry['result']
        
        return None

    def _calculate_cache_size(self) -> float:
        total_size = 0
        try:
            for filename in os.listdir(self.cache_dir):
                if filename.endswith('.pkl'):
                    filepath = os.path.join(self.cache_dir, filename)
                    total_size += os.path.getsize(filepath)
        except:
            pass
        return total_size / (1024 * 1024)

    def _clean_expired_cache(self):
        try:
            for filename in os.listdir(self.cache_dir):
                if filename.endswith('.pkl'):
                    filepath = os.path.join(self.cache_dir, filename)
                    try:
                        with open(filepath, 'rb') as f:
                            cached_data = pickle.load(f)

                        if time.time() - cached_data.get('timestamp', 0) > self.ttl_seconds:
                            os.remove(filepath)
                            self.stats['expired'] += 1

                            meta_file = filepath.replace('.pkl', '_meta.json')
                            if os.path.exists(meta_file):
                                os.remove(meta_file)

                    except:
                        try:
                            os.remove(filepath)
                        except:
                            pass

            cache_size = self._calculate_cache_size()
            if cache_size > Config.MAX_CACHE_SIZE_MB:
                self._evict_old_cache_items()

        except Exception as e:
            st.warning(f"⚠️ Cache cleanup error: {e}")

    def _evict_old_cache_items(self):
        try:
            cache_files = []
            for filename in os.listdir(self.cache_dir):
                if filename.endswith('.pkl'):
                    filepath = os.path.join(self.cache_dir, filename)
                    mtime = os.path.getmtime(filepath)
                    cache_files.append((mtime, filepath))

            cache_files.sort()

            cache_size = self._calculate_cache_size()
            while cache_files and cache_size > Config.MAX_CACHE_SIZE_MB * 0.8:
                _, old_file = cache_files.pop(0)

                try:
                    os.remove(old_file)
                    self.stats['evictions'] += 1

                    meta_file = old_file.replace('.pkl', '_meta.json')
                    if os.path.exists(meta_file):
                        os.remove(meta_file)

                except:
                    pass

                cache_size = self._calculate_cache_size()

        except Exception as e:
            st.warning(f"⚠️ Old cache item deletion error: {e}")

    def get(self, source: str, identifier: str, category: str = "default") -> Optional[Any]:
        failed_key = f"failed:{source}:{identifier}"
        if failed_key in self.failed_cache:
            failed_data = self.failed_cache[failed_key]
            if time.time() - failed_data['timestamp'] < self.failed_cache_ttl:
                return None

        key = self._get_cache_key(source, identifier)

        memory_key = f"{category}:{key}"
        if memory_key in self.memory_cache:
            data = self.memory_cache[memory_key]
            del self.memory_cache[memory_key]
            self.memory_cache[memory_key] = data
            self.stats['hits'] += 1
            self.stats['memory_hits'] += 1
            return data

        cache_path = self._get_cache_path(key)
        meta_path = self._get_cache_metadata_path(key)

        if os.path.exists(cache_path):
            try:
                with open(cache_path, 'rb') as f:
                    cached_data = pickle.load(f)

                if os.path.exists(meta_path):
                    try:
                        with open(meta_path, 'r') as mf:
                            metadata = json.load(mf)
                        category_match = metadata.get('category') == category
                    except:
                        category_match = True
                else:
                    category_match = True

                if (time.time() - cached_data.get('timestamp', 0) < self.ttl_seconds and
                    category_match):

                    if len(self.memory_cache) >= self.max_memory_items:
                        self.memory_cache.popitem(last=False)

                    self.memory_cache[memory_key] = cached_data['data']
                    self.stats['hits'] += 1
                    self.stats['file_hits'] += 1
                    return cached_data['data']
                else:
                    os.remove(cache_path)
                    if os.path.exists(meta_path):
                        os.remove(meta_path)
                    self.stats['expired'] += 1

            except:
                try:
                    os.remove(cache_path)
                    if os.path.exists(meta_path):
                        os.remove(meta_path)
                except:
                    pass

        self.stats['misses'] += 1
        return None

    def set(self, source: str, identifier: str, data: Any, category: str = "default", 
            stage: str = None, progress_data: Dict = None):
        """Расширенное кэширование с учетом этапа обработки"""
        key = self._get_cache_key(source, identifier)
        cache_path = self._get_cache_path(key)
        
        # Добавляем информацию о стадии обработки для возобновления
        cache_entry = {
            'timestamp': time.time(),
            'source': source,
            'identifier': identifier,
            'data': data,
            'category': category,
            'stage': stage,  # НОВОЕ: этап обработки
            'progress_data': progress_data  # НОВОЕ: данные о прогрессе
        }
        
        try:
            with open(cache_path, 'wb') as f:
                pickle.dump(cache_entry, f, protocol=pickle.HIGHEST_PROTOCOL)
            
            # Сохраняем метаданные отдельно для быстрого чтения
            metadata = {
                'category': category,
                'stage': stage,
                'created': datetime.now().isoformat(),
                'source': source,
                'identifier_hash': hashlib.md5(str(identifier).encode()).hexdigest(),
                'status': 'complete' if stage == 'final' else 'processing'
            }
            
            meta_path = self._get_cache_metadata_path(key)
            with open(meta_path, 'w') as mf:
                json.dump(metadata, mf, indent=2)
            
            # Также сохраняем в memory_cache
            memory_key = f"{category}:{stage}:{key}" if stage else f"{category}:{key}"
            if len(self.memory_cache) >= self.max_memory_items:
                self.memory_cache.popitem(last=False)
            
            self.memory_cache[memory_key] = data
            
            # Сохраняем прогресс для возможности возобновления
            if stage and stage != 'final':
                self._save_incremental_progress(identifier, stage, data)
            
        except Exception as e:
            st.warning(f"⚠️ Cache save error: {e}")

    def mark_as_failed(self, source: str, identifier: str, error: str = ""):
        failed_key = f"failed:{source}:{identifier}"
        self.failed_cache[failed_key] = {
            'timestamp': time.time(),
            'error': error,
            'source': source,
            'identifier': identifier
        }

    def _load_popular_dois(self):
        popular_file = os.path.join(self.cache_dir, "popular_dois.json")
        if os.path.exists(popular_file):
            try:
                with open(popular_file, 'r') as f:
                    self.popular_cache = json.load(f)
            except:
                self.popular_cache = {}

    def _save_popular_dois(self):
        popular_file = os.path.join(self.cache_dir, "popular_dois.json")
        try:
            with open(popular_file, 'w') as f:
                json.dump(self.popular_cache, f, indent=2)
        except:
            pass

    def update_popularity(self, doi: str):
        if doi in self.popular_cache:
            self.popular_cache[doi] += 1
        else:
            self.popular_cache[doi] = 1

        if len(self.popular_cache) % 100 == 0:
            self._save_popular_dois()

    def get_stats(self) -> Dict[str, Any]:
        cache_size = self._calculate_cache_size()
        total_requests = self.stats['hits'] + self.stats['misses']
        hit_ratio = (self.stats['hits'] / total_requests * 100) if total_requests > 0 else 0

        return {
            'hits': self.stats['hits'],
            'misses': self.stats['misses'],
            'expired': self.stats['expired'],
            'evictions': self.stats['evictions'],
            'memory_hits': self.stats['memory_hits'],
            'file_hits': self.stats['file_hits'],
            'api_calls_saved': self.stats['api_calls_saved'],
            'memory_items': len(self.memory_cache),
            'cache_size_mb': round(cache_size, 2),
            'hit_ratio': round(hit_ratio, 1),
            'failed_cache_size': len(self.failed_cache),
            'popular_dois': len(self.popular_cache)
        }

    def clear_all(self):
        try:
            for filename in os.listdir(self.cache_dir):
                filepath = os.path.join(self.cache_dir, filename)
                try:
                    os.remove(filepath)
                except:
                    pass

            self.memory_cache.clear()
            self.failed_cache.clear()
            self.popular_cache.clear()
            self.ror_cache = {'analyzed': {}, 'ref': {}, 'citing': {}, 'summary': {}}
            self.insights_cache = {
                'geo_bubbles': {}, 'temporal_patterns': {}, 'hyper_citation': {},
                'citation_cascades': {}, 'mutual_citations': {}
            }
            self.progress_cache = {
                'last_processed': {},
                'remaining_dois': {},
                'current_stage': {}
            }
            self.stats = {k: 0 for k in self.stats.keys()}

            st.success("✅ Cache completely cleared")

        except Exception as e:
            st.error(f"⚠️ Cache clear error: {e}")

    def get_ror_cache(self, category: str, query: str) -> Optional[Dict]:
        if category in self.ror_cache and query in self.ror_cache[category]:
            return self.ror_cache[category][query]
        return None

    def set_ror_cache(self, category: str, query: str, data: Dict):
        if category not in self.ror_cache:
            self.ror_cache[category] = {}
        self.ror_cache[category][query] = data

    def clear_ror_cache(self, category: str = None):
        if category:
            if category in self.ror_cache:
                self.ror_cache[category].clear()
        else:
            for cat in self.ror_cache:
                self.ror_cache[cat].clear()

    def get_insight_cache(self, insight_type: str, key: str) -> Optional[Dict]:
        if insight_type in self.insights_cache and key in self.insights_cache[insight_type]:
            return self.insights_cache[insight_type][key]
        return None

    def set_insight_cache(self, insight_type: str, key: str, data: Dict):
        if insight_type not in self.insights_cache:
            self.insights_cache[insight_type] = {}
        self.insights_cache[insight_type][key] = {
            'data': data,
            'timestamp': time.time()
        }

    def clear_insight_cache(self, insight_type: str = None):
        if insight_type:
            if insight_type in self.insights_cache:
                self.insights_cache[insight_type].clear()
        else:
            for insight in self.insights_cache:
                self.insights_cache[insight].clear()

    def save_incremental_progress(self, doi: str, stage: str, data: Dict):
        """Сохраняет инкрементальный прогресс обработки DOI"""
        progress_key = f"progress:{stage}:{doi}"
        progress_data = {
            'doi': doi,
            'stage': stage,
            'data': data,
            'timestamp': time.time(),
            'status': 'processing'  # или 'completed', 'failed'
        }
        
        # Сохраняем во временный кэш прогресса
        self.incremental_progress[progress_key] = progress_data
        
        # Периодически сохраняем на диск
        if len(self.incremental_progress) % 50 == 0:
            self._flush_progress_to_disk()
    
    def save_batch_progress(self, stage: str, batch_id: int, processed_dois: List[Dict], 
                           failed_dois: List[str], total_count: int):
        """Сохраняет прогресс обработки батча"""
        batch_key = f"batch:{stage}:{batch_id}"
        batch_data = {
            'stage': stage,
            'batch_id': batch_id,
            'processed_dois': processed_dois,
            'failed_dois': failed_dois,
            'processed_count': len(processed_dois),
            'failed_count': len(failed_dois),
            'total_count': total_count,
            'timestamp': time.time(),
            'completed': False
        }
        
        self.batch_progress[batch_key] = batch_data
        self._save_batch_progress_to_disk(batch_key, batch_data)
        
        # Save to disk
        progress_file = os.path.join(self.cache_dir, "progress_cache.json")
        try:
            with open(progress_file, 'w') as f:
                json.dump(self.progress_cache, f, indent=2)
        except:
            pass

    def load_progress(self) -> Tuple[Optional[str], List[str], List[str]]:
        """Load saved processing progress"""
        progress_file = os.path.join(self.cache_dir, "progress_cache.json")
        if os.path.exists(progress_file):
            try:
                with open(progress_file, 'r') as f:
                    self.progress_cache = json.load(f)
                
                stage = self.progress_cache.get('current_stage')
                if stage:
                    processed = self.progress_cache.get('last_processed', {}).get(stage, [])
                    remaining = self.progress_cache.get('remaining_dois', {}).get(stage, [])
                    return stage, processed, remaining
            except:
                pass
        return None, [], []

    def clear_progress(self):
        """Clear saved progress"""
        self.progress_cache = {
            'last_processed': {},
            'remaining_dois': {},
            'current_stage': {}
        }
        progress_file = os.path.join(self.cache_dir, "progress_cache.json")
        if os.path.exists(progress_file):
            try:
                os.remove(progress_file)
            except:
                pass

    def _load_progress_cache(self):
        """Load progress cache from disk during initialization"""
        progress_file = os.path.join(self.cache_dir, "progress_cache.json")
        if os.path.exists(progress_file):
            try:
                with open(progress_file, 'r') as f:
                    self.progress_cache = json.load(f)
            except:
                self.progress_cache = {
                    'last_processed': {},
                    'remaining_dois': {},
                    'current_stage': {}
                }

# ============================================================================
# 🚀 ADAPTIVE DELAY MANAGER
# ============================================================================

class AdaptiveDelayManager:
    def __init__(self, initial_delay: float = Config.INITIAL_DELAY):
        self.initial_delay = initial_delay
        self.current_delay = initial_delay
        self.max_delay = Config.MAX_DELAY
        self.min_delay = Config.MIN_DELAY
        self.success_count = 0
        self.failure_count = 0
        self.last_request_time = 0
        self.response_times = []

        self.stats = {
            'total_requests': 0,
            'successful_requests': 0,
            'failed_requests': 0,
            'avg_response_time': 0,
            'total_wait_time': 0
        }

    def wait_if_needed(self):
        current_time = time.time()
        elapsed = current_time - self.last_request_time

        if elapsed < self.current_delay:
            wait_time = self.current_delay - elapsed
            time.sleep(wait_time)
            self.stats['total_wait_time'] += wait_time

        self.last_request_time = time.time()
        return self.current_delay

    def update_delay(self, success: bool, response_time: float = None):
        self.stats['total_requests'] += 1

        if response_time:
            self.response_times.append(response_time)
            if len(self.response_times) > 10:
                self.response_times.pop(0)
            self.stats['avg_response_time'] = sum(self.response_times) / len(self.response_times)

        if success:
            self.success_count += 1
            self.failure_count = max(0, self.failure_count - 1)
            self.stats['successful_requests'] += 1

            if self.success_count >= 2:
                self.current_delay = max(self.min_delay, self.current_delay * 0.7)
                self.success_count = 0

        else:
            self.failure_count += 1
            self.success_count = 0
            self.stats['failed_requests'] += 1

            self.current_delay = min(self.max_delay, self.current_delay * 1.3)

        self.current_delay = min(self.max_delay, self.current_delay)

    def get_delay(self) -> float:
        return self.current_delay

    def get_stats(self) -> Dict[str, Any]:
        total_requests = self.stats['total_requests']
        success_rate = (self.stats['successful_requests'] / total_requests * 100) if total_requests > 0 else 0

        return {
            'current_delay': round(self.current_delay, 3),
            'total_requests': total_requests,
            'success_rate': round(success_rate, 1),
            'avg_response_time': round(self.stats['avg_response_time'], 3) if self.stats['avg_response_time'] > 0 else 0,
            'total_wait_time': round(self.stats['total_wait_time'], 2)
        }

# ============================================================================
# 📊 PROGRESS MONITOR (ADAPTED FOR STREAMLIT)
# ============================================================================

class ProgressMonitor:
    def __init__(self, total_items: int, stage_name: str = "Processing", progress_bar=None, status_text=None):
        self.total_items = total_items
        self.processed_items = 0
        self.start_time = time.time()
        self.stage_name = stage_name
        self.last_progress_time = self.start_time
        self.processing_speeds = []
        
        # Streamlit elements
        self.progress_bar = progress_bar
        self.status_text = status_text
        self.progress_container = None

        self.checkpoint_times = []
        self.checkpoint_items = []

        self.stats = {
            'success': 0,
            'failed': 0,
            'cached': 0,
            'skipped': 0
        }

    def update(self, count: int = 1, item_type: str = None):
        self.processed_items += count

        if item_type:
            if item_type in self.stats:
                self.stats[item_type] += count
            else:
                self.stats[item_type] = count

        # Update Streamlit progress bar
        if self.progress_bar is not None and self.total_items > 0:
            progress_percent = (self.processed_items / self.total_items) * 100
            self.progress_bar.progress(progress_percent / 100.0)
            
        # Update status text
        if self.status_text is not None:
            self._update_status_text()

        current_time = time.time()
        if current_time - self.last_progress_time > 10:
            self.last_progress_time = current_time

    def _update_status_text(self):
        if self.total_items == 0:
            return

        elapsed = time.time() - self.start_time
        progress_percent = (self.processed_items / self.total_items) * 100

        if elapsed > 0:
            speed = self.processed_items / elapsed
            self.processing_speeds.append(speed)
            if len(self.processing_speeds) > 5:
                self.processing_speeds.pop(0)

            avg_speed = sum(self.processing_speeds) / len(self.processing_speeds) if self.processing_speeds else speed
            items_per_min = avg_speed * 60

            remaining_items = self.total_items - self.processed_items
            if avg_speed > 0:
                eta_seconds = remaining_items / avg_speed
                eta_str = self._format_time(eta_seconds)
            else:
                eta_str = "calculating..."

            stats_str = ""
            for stat_type, count in self.stats.items():
                if count > 0:
                    stats_str += f", {stat_type}: {count}"

            status_message = f"{self.stage_name}: {self.processed_items}/{self.total_items} " \
                           f"({progress_percent:.1f}%), " \
                           f"speed: {items_per_min:.1f} DOI/min, " \
                           f"remaining: {eta_str}{stats_str}"
            
            if self.status_text is not None:
                self.status_text.text(status_message)

    def _format_time(self, seconds: float) -> str:
        if seconds < 60:
            return f"{seconds:.0f} sec"
        elif seconds < 3600:
            minutes = seconds / 60
            return f"{minutes:.0f} min"
        else:
            hours = seconds / 3600
            return f"{hours:.1f} hr"

    def get_summary(self) -> Dict[str, Any]:
        elapsed = time.time() - self.start_time

        if elapsed > 0:
            total_speed = self.processed_items / elapsed
            items_per_min = total_speed * 60
        else:
            items_per_min = 0

        return {
            'total_items': self.total_items,
            'processed_items': self.processed_items,
            'elapsed_time': round(elapsed, 1),
            'speed_per_min': round(items_per_min, 1),
            'success_count': self.stats.get('success', 0),
            'failed_count': self.stats.get('failed', 0),
            'cached_count': self.stats.get('cached', 0),
            'completion_percent': round((self.processed_items / self.total_items * 100), 1) if self.total_items > 0 else 0
        }

    def complete(self):
        elapsed = time.time() - self.start_time

        if self.total_items > 0:
            progress_percent = (self.processed_items / self.total_items) * 100
        else:
            progress_percent = 100

        summary = self.get_summary()

        if self.progress_bar is not None:
            self.progress_bar.progress(1.0)
            
        if self.status_text is not None:
            self.status_text.text(f"✅ {self.stage_name} completed! "
                                  f"Processed: {self.processed_items} ({progress_percent:.1f}%), "
                                  f"time: {self._format_time(elapsed)}")

        return summary

    def create_snapshot(self) -> Dict:
        """Создает снимок текущего состояния для восстановления"""
        return {
            'total_items': self.total_items,
            'processed_items': self.processed_items,
            'stage_name': self.stage_name,
            'stats': self.stats.copy(),
            'start_time': self.start_time,
            'checkpoint_times': self.checkpoint_times.copy(),
            'checkpoint_items': self.checkpoint_items.copy(),
            'timestamp': time.time()
        }
    
    def restore_from_snapshot(self, snapshot: Dict):
        """Восстанавливает состояние из снимка"""
        self.total_items = snapshot['total_items']
        self.processed_items = snapshot['processed_items']
        self.stage_name = snapshot['stage_name']
        self.stats = snapshot['stats']
        self.start_time = snapshot['start_time']
        self.checkpoint_times = snapshot['checkpoint_times']
        self.checkpoint_items = snapshot['checkpoint_items']
        
# ============================================================================
# 📝 FAILED DOI TRACKER
# ============================================================================

class FailedDOITracker:
    def __init__(self):
        self.failed_dois = {}
        self.relationships = defaultdict(list)
        self.sources = {}

        self.stats = {
            'total_failed': 0,
            'analyzed_failed': 0,
            'ref_failed': 0,
            'citing_failed': 0,
            'retry_failed': 0,
            'by_error_type': defaultdict(int)
        }

    def add_failed_doi(self, doi: str, error: str, source_type: str,
                       related_dois: List[str] = None, original_doi: str = None):

        self.failed_dois[doi] = {
            'doi': doi,
            'error': error,
            'source_type': source_type,
            'timestamp': datetime.now().isoformat(),
            'related_dois': related_dois or [],
            'original_doi': original_doi
        }

        self.sources[doi] = source_type

        if related_dois:
            self.relationships[doi].extend(related_dois)

        self.stats['total_failed'] += 1

        if source_type in self.stats:
            self.stats[f'{source_type}_failed'] += 1
        else:
            self.stats['by_error_type'][source_type] = self.stats['by_error_type'].get(source_type, 0) + 1

        self.stats['by_error_type'][error] += 1

    def get_failed_for_excel(self) -> List[Dict]:
        data = []

        for doi, info in self.failed_dois.items():
            relationship_info = ""
            if info['original_doi']:
                relationship_info = f"Source: {info['original_doi']}"
            elif info['related_dois']:
                relationship_info = f"Related to: {', '.join(info['related_dois'][:3])}"
                if len(info['related_dois']) > 3:
                    relationship_info += f"... (more {len(info['related_dois']) - 3})"

            row = {
                'DOI': doi,
                'Source Type': info['source_type'],
                'Error': info['error'],
                'Relationships': relationship_info,
                'Relationship Count': len(info['related_dois']),
                'Error Date': info['timestamp']
            }
            data.append(row)

        return data

    def get_stats(self) -> Dict[str, Any]:
        return {
            'total_failed': self.stats['total_failed'],
            'analyzed_failed': self.stats['analyzed_failed'],
            'ref_failed': self.stats['ref_failed'],
            'citing_failed': self.stats['citing_failed'],
            'retry_failed': self.stats['retry_failed'],
            'error_types': dict(self.stats['by_error_type']),
            'unique_failed_dois': len(self.failed_dois)
        }

    def clear(self):
        self.failed_dois.clear()
        self.relationships.clear()
        self.sources.clear()
        self.stats = {
            'total_failed': 0,
            'analyzed_failed': 0,
            'ref_failed': 0,
            'citing_failed': 0,
            'retry_failed': 0,
            'by_error_type': defaultdict(int)
        }

# ============================================================================
# 🌐 API CLIENTS
# ============================================================================

class APIClient:
    def __init__(self, cache_manager: SmartCacheManager, delay_manager: AdaptiveDelayManager):
        self.cache = cache_manager
        self.delay = delay_manager
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'ArticleAnalyzer/3.0 (colab-user@example.com)',
            'Accept': 'application/json',
            'Accept-Encoding': 'gzip'
        })

    def make_request(self, url: str, cache_key: str, params: Dict = None,
                    timeout: int = Config.REQUEST_TIMEOUT, category: str = "api") -> Dict:

        full_cache_key = f"{url}:{hash(str(params) if params else '')}"

        cached_data = self.cache.get(category, full_cache_key)
        if cached_data is not None:
            return cached_data

        wait_time = self.delay.wait_if_needed()

        try:
            start_time = time.time()
            response = self.session.get(url, params=params, timeout=timeout)
            response_time = time.time() - start_time

            if response.status_code == 200:
                data = response.json()

                self.cache.set(category, full_cache_key, data)
                self.delay.update_delay(True, response_time)
                return data

            elif response.status_code == 429:
                self.delay.current_delay = min(self.delay.max_delay, self.delay.current_delay * 1.5)
                self.delay.update_delay(False, response_time)
                return {"error": f"Rate limit exceeded, wait {self.delay.current_delay:.1f}s", "status": 429}

            else:
                self.delay.update_delay(False, response_time)
                return {"error": f"API error {response.status_code}", "status": response.status_code}

        except requests.exceptions.Timeout:
            self.delay.update_delay(False, Config.REQUEST_TIMEOUT)
            return {"error": "Request timeout"}
        except Exception as e:
            self.delay.update_delay(False, 0)
            return {"error": f"Request failed: {str(e)}"}

class CrossrefClient(APIClient):
    def __init__(self, cache_manager: SmartCacheManager, delay_manager: AdaptiveDelayManager):
        super().__init__(cache_manager, delay_manager)
        self.base_url = Config.CROSSREF_URL

    def fetch_article(self, doi: str) -> Dict:
        clean_doi = self._clean_doi(doi)
        if not clean_doi:
            return {"error": "Invalid DOI"}

        url = f"{self.base_url}{clean_doi}"
        return self.make_request(url, f"crossref:{clean_doi}", category="crossref")

    def fetch_references(self, doi: str) -> List[str]:
        clean_doi = self._clean_doi(doi)
        if not clean_doi:
            return []

        data = self.fetch_article(clean_doi)
        references = []

        if 'message' in data and 'reference' in data['message']:
            for ref in data['message']['reference']:
                if 'DOI' in ref and ref['DOI']:
                    ref_doi = self._clean_doi(ref['DOI'])
                    if ref_doi:
                        references.append(ref_doi)

        return references

    def fetch_citations(self, doi: str) -> List[str]:
        clean_doi = self._clean_doi(doi)
        if not clean_doi:
            return []

        citing_dois = []
        try:
            url = f"{self.base_url}{clean_doi}"
            params = {'filter': 'has-reference:1'}
            data = self.make_request(url, f"crossref_citations:{clean_doi}", params=params)

            if 'message' in data and 'is-referenced-by' in data['message']:
                references = data['message']['is-referenced-by']
                for ref in references:
                    if isinstance(ref, dict) and 'DOI' in ref:
                        citing_doi = self._clean_doi(ref['DOI'])
                        if citing_doi:
                            citing_dois.append(citing_doi)

        except Exception as e:
            st.warning(f"Crossref citations error for {doi}: {e}")

        return citing_dois

    def _clean_doi(self, doi: str) -> str:
        if not doi or not isinstance(doi, str):
            return ""

        doi = doi.strip()
        prefixes = ['doi:', 'DOI:', 'https://doi.org/', 'http://doi.org/', 'https://dx.doi.org/', 'http://dx.doi.org/']

        for prefix in prefixes:
            if doi.lower().startswith(prefix.lower()):
                doi = doi[len(prefix):]

        return doi.strip()

# ============================================================================
# 🌐 UPDATED API CLIENTS
# ============================================================================

class OpenAlexClient(APIClient):
    def __init__(self, cache_manager: SmartCacheManager, delay_manager: AdaptiveDelayManager):
        super().__init__(cache_manager, delay_manager)
        self.base_url = Config.OPENALEX_URL
        self.works_url = Config.OPENALEX_WORKS_URL

    def fetch_article(self, doi: str) -> Dict:
        clean_doi = self._clean_doi(doi)
        if not clean_doi:
            return {"error": "Invalid DOI"}

        url = f"{self.base_url}{clean_doi}"
        return self.make_request(url, f"openalex:{clean_doi}", category="openalex")

    def fetch_citations(self, doi: str, max_pages: int = 10) -> List[str]:
        """
        Old citation collection logic - used for reference and citing articles
        Collects only up to 2000 citations (200 * max_pages)
        """
        clean_doi = self._clean_doi(doi)
        if not clean_doi:
            return []

        citing_dois = []

        try:
            article_data = self.fetch_article(clean_doi)
            if 'error' in article_data:
                return []

            article_id = article_data.get('id', '').split('/')[-1]
            if not article_id:
                return []

            params = {
                'filter': f'cites:{article_id}',
                'per-page': 200,
                'select': 'doi,title,publication_year'
            }

            page = 1
            has_more = True

            while has_more and page <= max_pages:
                self.delay.wait_if_needed()

                response = self.session.get(self.works_url, params=params)
                if response.status_code == 200:
                    data = response.json()

                    for work in data.get('results', []):
                        if work.get('doi'):
                            citing_doi = self._clean_doi(work['doi'])
                            if citing_doi:
                                citing_dois.append(citing_doi)

                    if 'meta' in data and data['meta'].get('next_cursor'):
                        params['cursor'] = data['meta']['next_cursor']
                        page += 1
                        time.sleep(0.1)
                    else:
                        has_more = False
                else:
                    has_more = False

        except Exception as e:
            st.warning(f"OpenAlex citations error for {doi}: {e}")

        return list(set(citing_dois))

    def fetch_all_citations_for_analyzed_article(self, doi: str) -> List[str]:
        """
        NEW LOGIC: Complete collection of ALL citations for analyzed articles
        Uses cursor-based pagination and collects all pages
        """
        clean_doi = self._clean_doi(doi)
        if not clean_doi:
            return []

        # Check cache for full citations
        cache_key = f"full_citations:{clean_doi}"
        cached_result = self.cache.get("full_citations", cache_key)
        if cached_result is not None:
            return cached_result

        try:
            # First get work_id from DOI
            article_data = self.fetch_article(clean_doi)
            if 'error' in article_data:
                return []

            article_id = article_data.get('id', '').split('/')[-1]
            if not article_id:
                return []

            all_citing_dois = []
            cursor = "*"
            page_num = 1
            max_retries = 3
            total_collected = 0

            while cursor:
                for attempt in range(max_retries):
                    try:
                        url = f"{self.works_url}?filter=cites:{article_id}&per-page=200&cursor={cursor}"
                        self.delay.wait_if_needed()

                        start_time = time.time()
                        response = self.session.get(url, timeout=45)
                        response_time = time.time() - start_time

                        if response.status_code == 200:
                            self.delay.update_delay(True, response_time)
                            data = response.json()

                            if not isinstance(data, dict):
                                st.warning(f"⚠️ Invalid response format on page {page_num} for {clean_doi}")
                                break

                            works = data.get('results', [])

                            if not works:
                                cursor = None
                                break

                            page_citing_dois = []
                            for work in works:
                                if isinstance(work, dict) and work.get('doi'):
                                    citing_doi = self._clean_doi(work['doi'])
                                    if citing_doi:
                                        page_citing_dois.append(citing_doi)

                            all_citing_dois.extend(page_citing_dois)
                            total_collected += len(page_citing_dois)

                            # Get next cursor
                            meta = data.get('meta', {})
                            next_cursor = meta.get('next_cursor')

                            if next_cursor:
                                cursor = next_cursor
                                page_num += 1
                                time.sleep(0.5)  # Pause between pages for rate limits
                            else:
                                cursor = None

                            break  # Success, exit retry loop

                        elif response.status_code == 429:
                            self.delay.update_delay(False, response_time)
                            wait_time = 2 ** (attempt + 1)  # Exponential backoff
                            time.sleep(wait_time)
                            continue

                        elif response.status_code == 404:
                            st.warning(f"⚠️ Article {clean_doi} not found in OpenAlex")
                            cursor = None
                            break

                        else:
                            self.delay.update_delay(False, response_time)
                            time.sleep(5)
                            continue

                    except requests.exceptions.Timeout:
                        time.sleep(5)
                        continue

                    except Exception as e:
                        time.sleep(5)
                        continue

                else:  # All retries exhausted
                    break

            # Remove duplicates and save to cache
            unique_citing_dois = list(set(all_citing_dois))

            # Save to cache with separate category for full citations
            self.cache.set("full_citations", cache_key, unique_citing_dois, category="full_citations_analyzed")

            return unique_citing_dois

        except Exception as e:
            st.error(f"❌ Critical error collecting citations for {clean_doi}: {str(e)}")
            return []

    def _safe_get(self, data, *keys, default=''):
        """Safe value extraction from dictionary (helper function)"""
        if not isinstance(data, dict):
            return default

        current = data
        for key in keys:
            if isinstance(current, dict):
                current = current.get(key)
            else:
                return default

        return current if current is not None else default

    def _clean_doi(self, doi: str) -> str:
        if not doi or not isinstance(doi, str):
            return ""

        doi = doi.strip()
        prefixes = ['doi:', 'DOI:', 'https://doi.org/', 'http://doi.org/', 'https://dx.doi.org/', 'http://dx.doi.org/']

        for prefix in prefixes:
            if doi.lower().startswith(prefix.lower()):
                doi = doi[len(prefix):]

        return doi.strip()

# ============================================================================
# 🔍 UPDATED RORClient (WITH PARALLEL PROCESSING)
# ============================================================================

class RORClient:
    def __init__(self, cache_manager: SmartCacheManager):
        self.cache = cache_manager
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'ArticleAnalyzer-ROR/3.0 (colab-user@example.com)',
            'Accept': 'application/json'
        })
        self.last_request_time = 0
        self.min_delay = 0.3
        self.parallel_workers = 10  # Number of parallel threads for ROR API

    def _respect_delay(self):
        elapsed = time.time() - self.last_request_time
        if elapsed < self.min_delay:
            time.sleep(self.min_delay - elapsed)
        self.last_request_time = time.time()

    def search_organization(self, query: str, category: str = "summary") -> Dict[str, str]:
        """Main method for searching organization in ROR"""
        if not query or len(query.strip()) < 2:
            return self._create_empty_result()

        cache_key = f"ror_search:{query.strip().lower()}"

        if category != "summary":
            cached = self.cache.get_ror_cache(category, cache_key)
            if cached is not None:
                return cached

        cached = self.cache.get("ror_search", cache_key)
        if cached is not None:
            if cached.get('ror_id'):
                if category != "summary":
                    self.cache.set_ror_cache(category, cache_key, cached)
                return cached

        self._respect_delay()

        try:
            response = self.session.get(
                Config.ROR_API_URL,
                params={'query': query.strip()},
                timeout=10
            )

            if response.status_code != 200:
                return self._create_empty_result()

            data = response.json()
            items = data.get('items', [])

            if not items:
                return self._create_empty_result()

            best = self._improved_find_best_match(query.strip(), items)
            if not best:
                return self._create_empty_result()

            colab_url = ""
            try:
                ror_id = best['id'].split('/')[-1]
                colab_url = f"https://colab.ws/organizations/{ror_id}"
            except:
                pass

            website = ""
            try:
                links = best.get('links', []) or []
                for link in links:
                    url = (link.get('value') or link.get('url') if isinstance(link, dict) else str(link)) if link else None
                    if url and isinstance(url, str):
                        url = url.strip()
                        website = url if url.startswith('http') else 'https://' + url
                        break
            except:
                pass

            result = {
                'ror_id': colab_url,
                'website': website,
                'score': best.get('score', 0),
                'name': best.get('name', ''),
                'acronyms': best.get('acronyms', [])
            }

            if colab_url:
                self.cache.set("ror_search", cache_key, result, category="ror_search")
                if category != "summary":
                    self.cache.set_ror_cache(category, cache_key, result)

            return result

        except Exception as e:
            st.warning(f"ROR error for query '{query}': {e}")
            return self._create_empty_result()

    def search_organization_parallel(self, query: str) -> Dict[str, str]:
        """Wrapper for parallel processing"""
        return self.search_organization(query, "summary")
        
    def search_multiple_organizations(self, queries: List[str], progress_container=None) -> Dict[str, Dict[str, str]]:
        """Parallel search for multiple organizations"""
        results = {}
        
        if not queries:
            st.warning("ROR search query list is empty")
            return results
        
        # Remove duplicates
        unique_queries = list(set(queries))
        
        # Setup progress bar
        if progress_container:
            # Create new progress elements inside container
            progress_text = progress_container.text(f"🔍 Searching ROR data for {len(unique_queries)} affiliations...")
            ror_progress_bar = progress_container.progress(0)
            status_text = progress_container.empty()
            
            # Update initial status
            status_text.text(f"🔍 Initializing search...")
        else:
            progress_text = None
            ror_progress_bar = None
            status_text = None
        
        st.info(f"Starting ROR search for {len(unique_queries)} unique affiliations...")
        
        # Use ThreadPoolExecutor for parallel processing
        with ThreadPoolExecutor(max_workers=self.parallel_workers) as executor:
            # Create dictionary future -> query
            future_to_query = {}
            for query in unique_queries:
                future = executor.submit(self.search_organization_parallel, query)
                future_to_query[future] = query
            
            # Process results as they arrive
            completed = 0
            total = len(unique_queries)
            
            for future in concurrent.futures.as_completed(future_to_query):
                query = future_to_query[future]
                try:
                    result = future.result()
                    if result and result.get('ror_id'):
                        results[query] = result
                        if len(results) % 10 == 0 and status_text:
                            status_text.text(f"🔍 Found {len(results)} ROR records...")
                    elif result and not result.get('ror_id'):
                        # Record results even if no ROR ID found
                        results[query] = result
                except Exception as e:
                    st.warning(f"ROR search error for '{query}': {e}")
                    # Create empty record in case of error
                    results[query] = {'ror_id': '', 'website': '', 'score': 0, 'name': '', 'acronyms': []}
                
                completed += 1
                if ror_progress_bar and total > 0:
                    progress_percent = completed / total
                    ror_progress_bar.progress(progress_percent)
                    if status_text:
                        status_text.text(f"🔍 Processed: {completed}/{total} ({progress_percent*100:.1f}%), ROR found: {len([r for r in results.values() if r.get('ror_id')])}")
        
        if ror_progress_bar:
            ror_progress_bar.progress(1.0)
            if status_text:
                status_text.text(f"✅ ROR data collected for {len(results)} affiliations (ROR ID found: {len([r for r in results.values() if r.get('ror_id')])})")
        
        st.success(f"✅ ROR search completed. Found {len([r for r in results.values() if r.get('ror_id')])} ROR ID from {len(unique_queries)} queries")
        
        return results
    
    def _improved_find_best_match(self, query: str, items: List[Dict]) -> Optional[Dict]:
        if not items:
            return None

        q = query.strip().lower()
        best_item = None
        best_score = -1

        strategies = [
            self._strategy_exact_match,
            self._strategy_partial_match,
            self._strategy_acronym_match,
            self._strategy_fuzzy_match
        ]

        for item in items:
            score = 0
            name = item.get('name', '').lower()
            aliases = [a.lower() for a in item.get('aliases', [])]
            acronyms = [a.lower() for a in item.get('acronyms', []) if a]

            for strategy in strategies:
                strategy_score = strategy(q, name, aliases, acronyms)
                if strategy_score > score:
                    score = strategy_score

            ror_score = item.get('score', 0) * 50

            final_score = max(score, ror_score)

            if final_score > best_score:
                best_score = final_score
                best_item = item

        return best_item

    def _strategy_exact_match(self, query: str, name: str, aliases: List[str], acronyms: List[str]) -> int:
        if query == name or query in aliases:
            return 10000
        return 0

    def _strategy_partial_match(self, query: str, name: str, aliases: List[str], acronyms: List[str]) -> int:
        all_texts = [name] + aliases + acronyms
        for text in all_texts:
            if query in text or text in query:
                return 9000
        return 0

    def _strategy_acronym_match(self, query: str, name: str, aliases: List[str], acronyms: List[str]) -> int:
        if query in acronyms:
            return 9500
        return 0

    def _strategy_fuzzy_match(self, query: str, name: str, aliases: List[str], acronyms: List[str]) -> int:
        all_texts = [name] + aliases
        best_fuzzy = 0
        for text in all_texts:
            if text:
                score = fuzz.token_set_ratio(query, text)
                if score > best_fuzzy:
                    best_fuzzy = score
        return best_fuzzy

    def _create_empty_result(self) -> Dict[str, str]:
        return {
            'ror_id': '',
            'website': '',
            'score': 0,
            'name': '',
            'acronyms': []
        }

# ============================================================================
# 🛠️ DATA PROCESSOR
# ============================================================================

class DataProcessor:
    def __init__(self, cache_manager: SmartCacheManager):
        self.cache = cache_manager
        self.country_codes = Config.COUNTRY_CODES

    def extract_article_info(self, crossref_data: Dict, openalex_data: Dict,
                           doi: str, references: List[str], citations: List[str]) -> Dict:
    
        pub_info = self._extract_publication_info(crossref_data, openalex_data)
        authors, countries_from_auth = self._extract_authors_info(crossref_data, openalex_data)
        countries = self._extract_countries_info(authors, openalex_data)
    
        country_codes = [self._country_to_code(c) for c in countries]
        country_codes = list(set(filter(None, country_codes)))
    
        orcid_urls = []
        # NEW: collect author countries
        author_countries = []
        for author in authors:
            if author.get('orcid'):
                orcid_url = self._format_orcid_id(author['orcid'])
                if orcid_url:
                    orcid_urls.append(orcid_url)
            
            # Add author country if defined
            if author.get('author_country'):
                author_countries.append(author['author_country'])
    
        pages_field = pub_info['pages']
        if not pages_field and pub_info['article_number']:
            pages_field = f"Article {pub_info['article_number']}"
    
        # Extract topic information from OpenAlex
        topics_info = self._extract_topics_info(openalex_data)
    
        # Check reference count via OpenAlex if Crossref shows 0
        references_count = len(references)
        if references_count == 0 and openalex_data and 'referenced_works_count' in openalex_data:
            references_count = openalex_data.get('referenced_works_count', 0)
    
        quick_insights = self._extract_quick_insights(
            authors, countries, references, citations, pub_info
        )
    
        return {
            'doi': doi,
            'publication_info': pub_info,
            'topics_info': topics_info,
            'authors': authors,
            'countries': country_codes,
            'author_countries': list(set(author_countries)),  # NEW: author countries
            'orcid_urls': orcid_urls,
            'references': references,
            'citations': citations,
            'references_count': references_count,
            'pages_formatted': pages_field,
            'status': 'success',
            'quick_insights': quick_insights
        }

    def _extract_topics_info(self, openalex_data: Dict) -> Dict:
        """Extract topic, subfield, field, domain and concepts information from OpenAlex"""
        topics_info = {
            'topic': '',
            'subfield': '',
            'field': '',
            'domain': '',
            'concepts': []
        }

        if not openalex_data:
            return topics_info

        try:
            # Extract concepts
            concepts = openalex_data.get('concepts', [])
            concept_names = []
            
            for concept in concepts:
                if isinstance(concept, dict):
                    display_name = concept.get('display_name', '')
                    if display_name:
                        concept_names.append(display_name)
            
            topics_info['concepts'] = concept_names

            # Extract topic information (use first concept as topic)
            if concept_names:
                topics_info['topic'] = concept_names[0] if concept_names else ''
                
                # For subfield, field and domain use concept hierarchy
                # In real application need to extract from 'subfield', 'field', 'domain' fields
                # but in OpenAlex they are often within concepts
                if len(concept_names) > 1:
                    topics_info['subfield'] = concept_names[1] if len(concept_names) > 1 else ''
                if len(concept_names) > 2:
                    topics_info['field'] = concept_names[2] if len(concept_names) > 2 else ''
                if len(concept_names) > 3:
                    topics_info['domain'] = concept_names[3] if len(concept_names) > 3 else ''

            # Check for fields in OpenAlex structure
            if 'topics' in openalex_data and openalex_data['topics']:
                topics = openalex_data['topics']
                if isinstance(topics, list) and topics:
                    if isinstance(topics[0], dict):
                        topics_info['topic'] = topics[0].get('display_name', topics_info['topic'])

            if 'subfield' in openalex_data and openalex_data['subfield']:
                subfield = openalex_data['subfield']
                if isinstance(subfield, dict):
                    topics_info['subfield'] = subfield.get('display_name', topics_info['subfield'])
                elif isinstance(subfield, str):
                    topics_info['subfield'] = subfield

            if 'field' in openalex_data and openalex_data['field']:
                field = openalex_data['field']
                if isinstance(field, dict):
                    topics_info['field'] = field.get('display_name', topics_info['field'])
                elif isinstance(field, str):
                    topics_info['field'] = field

            if 'domain' in openalex_data and openalex_data['domain']:
                domain = openalex_data['domain']
                if isinstance(domain, dict):
                    topics_info['domain'] = domain.get('display_name', topics_info['domain'])
                elif isinstance(domain, str):
                    topics_info['domain'] = domain

        except Exception as e:
            st.warning(f"⚠️ Topics info extraction error: {e}")

        return topics_info

    def _extract_quick_insights(self, authors: List[Dict], countries: List[str],
                               references: List[str], citations: List[str],
                               pub_info: Dict) -> Dict:
        current_year = datetime.now().year

        try:
            pub_year = int(pub_info.get('year', current_year))
            article_age = current_year - pub_year
        except:
            article_age = 0

        insights = {
            'author_count': len(authors),
            'country_count': len(countries),
            'reference_count': len(references),
            'citation_count': len(citations),
            'publication_year': pub_info.get('year', ''),
            'article_age': article_age,
            'citation_velocity': 0,
            'geographic_diversity': len(countries) / max(1, len(authors)),
            'self_citation_risk': 0,
            'intra_affiliation_citation_ratio': 0
        }

        if article_age > 0 and citations:
            insights['citation_velocity'] = len(citations) / article_age

        return insights

    def _extract_publication_info(self, crossref_data: Dict, openalex_data: Dict) -> Dict:
        pub_info = {
            'title': '',
            'journal': '',
            'publication_date': '',
            'year': '',
            'volume': '',
            'pages': '',
            'article_number': '',
            'citation_count_crossref': 0,
            'citation_count_openalex': 0,
            'doi': ''
        }

        if 'message' in crossref_data:
            msg = crossref_data['message']

            pub_info['doi'] = msg.get('DOI', '')
            pub_info['title'] = msg.get('title', [''])[0] if msg.get('title') else ''
            pub_info['journal'] = msg.get('container-title', [''])[0] if msg.get('container-title') else ''

            # Improved date parsing from Crossref
            pub_date = None
            if 'created' in msg and 'date-parts' in msg['created']:
                created_date = msg.get('created', {})
                if 'date-parts' in created_date and created_date['date-parts']:
                    pub_date = created_date['date-parts'][0]

            # If not found in created, use license as fallback
            if not pub_date and 'license' in msg:
                for license_item in msg['license']:
                    if isinstance(license_item, dict) and 'start' in license_item:
                        start_date = license_item.get('start', {})
                        if 'date-parts' in start_date and start_date['date-parts']:
                            pub_date = start_date['date-parts'][0]
                            break

            # If not found in license, search in created
            if not pub_date and 'created' in msg:
                created_date = msg.get('created', {})
                if 'date-parts' in created_date and created_date['date-parts']:
                    pub_date = created_date['date-parts'][0]

            # If not found in created, use old logic
            if not pub_date and 'published' in msg and 'date-parts' in msg['published']:
                pub_date = msg['published']['date-parts'][0]

            if pub_date:
                pub_info['year'] = str(pub_date[0])
                if len(pub_date) >= 2:
                    month = str(pub_date[1]).zfill(2)
                    if len(pub_date) >= 3:
                        day = str(pub_date[2]).zfill(2)
                        pub_info['publication_date'] = f"{pub_info['year']}-{month}-{day}"
                    else:
                        pub_info['publication_date'] = f"{pub_info['year']}-{month}-15"
                else:
                    pub_info['publication_date'] = f"{pub_info['year']}-01-01"

            pub_info['volume'] = msg.get('volume', '')
            pub_info['pages'] = msg.get('page', '')
            pub_info['article_number'] = msg.get('article-number', '')
            pub_info['citation_count_crossref'] = msg.get('is-referenced-by-count', 0)

        if 'title' in openalex_data:
            pub_info['title'] = pub_info['title'] or openalex_data.get('title', '')

        if 'primary_location' in openalex_data:
            source = openalex_data['primary_location'].get('source', {})
            pub_info['journal'] = pub_info['journal'] or source.get('display_name', '')

        if 'publication_year' in openalex_data:
            pub_info['year'] = pub_info['year'] or str(openalex_data.get('publication_year', ''))

        if 'biblio' in openalex_data:
            biblio = openalex_data['biblio']
            pub_info['volume'] = pub_info['volume'] or biblio.get('volume', '')
            if not pub_info['pages']:
                pub_info['pages'] = biblio.get('first_page', '') + '-' + biblio.get('last_page', '') \
                                    if biblio.get('first_page') else biblio.get('pages', '')

        pub_info['citation_count_openalex'] = openalex_data.get('cited_by_count', 0)

        return pub_info

    def _extract_authors_info(self, crossref_data: Dict, openalex_data: Dict) -> Tuple[List[Dict], List[str]]:
        authors = []
        countries = []
    
        try:
            if openalex_data and 'authorships' in openalex_data:
                for authorship in openalex_data['authorships']:
                    if not authorship:
                        continue
    
                    author_display = authorship.get('author', {})
                    full_name = authorship.get('raw_author_name') or author_display.get('display_name', '')
    
                    if not full_name:
                        continue
    
                    author_info = {
                        'name': full_name,
                        'affiliation': [],
                        'orcid': author_display.get('orcid', ''),
                        'author_country': ''  # NEW: add author country
                    }
    
                    institutions = authorship.get('institutions', [])
                    institution_countries = []
                    
                    if institutions:
                        for inst in institutions:
                            if inst and isinstance(inst, dict):
                                display_name = inst.get('display_name')
                                if display_name:
                                    clean_aff = self._clean_affiliation(display_name)
                                    if clean_aff:
                                        author_info['affiliation'].append(clean_aff)
                                
                                # NEW LOGIC: determine country from institution
                                country_code = inst.get('country_code')
                                if country_code and country_code != 'XX':
                                    institution_countries.append(country_code)
                                    countries.append(country_code)
                                
                                # If no country_code, try to determine from name
                                elif display_name:
                                    country_from_name = self._get_country_from_institution_name(display_name)
                                    if country_from_name:
                                        institution_countries.append(country_from_name)
                                        countries.append(country_from_name)
                    
                    # Determine author country: take first country from his institutions
                    if institution_countries:
                        author_info['author_country'] = institution_countries[0]
                        
                    # Fallback: if not found through institutions, determine from affiliation name
                    if not author_info['author_country'] and author_info['affiliation']:
                        for affiliation in author_info['affiliation']:
                            country_from_aff = self._get_country_from_institution_name(affiliation)
                            if country_from_aff:
                                author_info['author_country'] = country_from_aff
                                break
    
                    authors.append(author_info)
        except Exception as e:
            st.warning(f"⚠️ OpenAlex author extraction error: {e}")
    
        if not authors and crossref_data:
            try:
                message = crossref_data.get('message', {})
                crossref_authors = message.get('author', [])
    
                if crossref_authors:
                    for author_obj in crossref_authors:
                        if not author_obj:
                            continue
    
                        given = author_obj.get('given', '')
                        family = author_obj.get('family', '')
                        full_name = f"{given} {family}".strip()
    
                        if not full_name:
                            continue
    
                        author_info = {
                            'name': full_name,
                            'affiliation': [],
                            'orcid': author_obj.get('ORCID', ''),
                            'author_country': ''  # NEW: add author country
                        }
    
                        affiliations = author_obj.get('affiliation', [])
                        affiliation_countries = []
                        
                        if affiliations:
                            for affil in affiliations:
                                if affil and isinstance(affil, dict):
                                    affil_name = affil.get('name')
                                    if affil_name:
                                        clean_aff = self._clean_affiliation(affil_name)
                                        if clean_aff:
                                            author_info['affiliation'].append(clean_aff)
                                            
                                            # NEW LOGIC: determine country from affiliation
                                            country_from_aff = self._get_country_from_institution_name(clean_aff)
                                            if country_from_aff:
                                                affiliation_countries.append(country_from_aff)
                                                countries.append(country_from_aff)
                        
                        # Determine author country from his affiliations
                        if affiliation_countries:
                            author_info['author_country'] = affiliation_countries[0]
                        
                        # If not found, try to determine from name
                        if not author_info['author_country'] and full_name:
                            # For Crossref data it's more complex, skip
                            pass
    
                        authors.append(author_info)
            except Exception as e:
                st.warning(f"⚠️ Crossref author extraction error: {e}")
    
        return authors, list(set(countries))
    
    def _get_country_from_institution_name(self, institution_name: str) -> str:
        """Determine country from institution name"""
        if not institution_name:
            return ""
        
        institution_lower = institution_name.lower()
        
        # First check for explicit country mentions
        for country_name, country_code in self.country_codes.items():
            country_lower = country_name.lower()
            pattern = r'\b' + re.escape(country_lower) + r'\b'
            if re.search(pattern, institution_lower):
                return country_code
        
        # Check country codes
        for country_name, country_code in self.country_codes.items():
            if len(country_code) == 2:
                if re.search(r'\b' + re.escape(country_code) + r'\b', institution_name, re.IGNORECASE):
                    return country_code
        
        # Check Russian variants
        if re.search(r'\b(росси|рф|русск|москв|спб|сибир|урал)\b', institution_lower):
            return 'RU'
        
        # Check Chinese variants
        if re.search(r'\b(china|chinese|beijing|shanghai|peking|zhejiang|tsinghua|fudan)\b', institution_lower):
            return 'CN'
        
        # Check American
        if re.search(r'\b(usa|united states|us | u\.s\.|california|massachusetts|harvard|mit|stanford)\b', institution_lower):
            return 'US'
        
        return ""

    def _extract_author_from_crossref(self, full_name: Optional[str], crossref_data: Dict, author_obj: Dict = None) -> Optional[Dict]:
        if author_obj is None:
            return None

        given = author_obj.get('given', '')
        family = author_obj.get('family', '')
        name = f"{given} {family}".strip() if given or family else full_name

        if not name:
            return None

        author_info = {
            'name': name,
            'affiliation': [],
            'orcid': author_obj.get('ORCID', '')
        }

        if 'affiliation' in author_obj:
            for affil in author_obj['affiliation']:
                if 'name' in affil:
                    clean_aff = self._clean_affiliation(affil['name'])
                    if clean_aff and clean_aff not in author_info['affiliation']:
                        author_info['affiliation'].append(clean_aff)

        return author_info

    def _clean_affiliation(self, affiliation: str) -> str:
        if not affiliation:
            return ""

        patterns_to_remove = [
            r',\s*[A-Z]{2}$',
            r',\s*[A-Z]{2}\s*\d+',
            r',\s*USA$', r',\s*United States$',
            r',\s*UK$', r',\s*United Kingdom$',
            r',\s*China$', r',\s*Россия$', r',\s*Russia$',
            r'\s*\([^)]*[Cc]ountry[^)]*\)',
            r'\s*\[[^\]]*[Cc]ountry[^\]]*\]',
            r'\b\d{5,6}(-\d{4})?\b',
        ]

        clean_aff = affiliation
        for pattern in patterns_to_remove:
            clean_aff = re.sub(pattern, '', clean_aff, flags=re.IGNORECASE)

        clean_aff = re.sub(r',\s*,', ',', clean_aff)
        clean_aff = clean_aff.strip(' ,;')

        return clean_aff if clean_aff and len(clean_aff) > 2 else affiliation

    def _extract_countries_info(self, authors: List[Dict], openalex_data: Dict) -> List[str]:
        countries = []

        if 'authorships' in openalex_data:
            for authorship in openalex_data['authorships']:
                for inst in authorship.get('institutions', []):
                    if 'country_code' in inst and inst['country_code']:
                        countries.append(inst['country_code'])
        
        if not countries:
            for author in authors:
                for affil in author['affiliation']:
                    for country_name, country_code in self.country_codes.items():
                        if country_name.lower() in affil.lower():
                            countries.append(country_code)
                            break

        return list(set(countries))

    def _country_to_code(self, country_name: str) -> str:
        if not country_name:
            return ""

        for name, code in self.country_codes.items():
            if country_name.lower() == name.lower():
                return code

        for name, code in self.country_codes.items():
            if name.lower() in country_name.lower():
                return code

        return country_name[:2].upper() if len(country_name) >= 2 else country_name.upper()

    def _format_orcid_id(self, orcid_id: str) -> str:
        if not orcid_id:
            return ""

        if orcid_id.startswith('https://orcid.org/'):
            return orcid_id

        clean_id = re.sub(r'[^\dXx-]', '', orcid_id.strip())

        if '-' in clean_id:
            return f"https://orcid.org/{clean_id}"
        elif len(clean_id) == 16:
            formatted = f"{clean_id[:4]}-{clean_id[4:8]}-{clean_id[8:12]}-{clean_id[12:]}"
            return f"https://orcid.org/{formatted}"
        else:
            return f"https://orcid.org/{clean_id}"

    def normalize_author_name(self, full_name: str) -> str:
        if not full_name:
            return ""

        name = re.sub(r'\s+', ' ', full_name.strip().replace(',', ' '))
        parts = name.split()

        if len(parts) == 0:
            return ""
        if len(parts) == 1:
            return parts[0]

        family = parts[-1]

        for part in parts[:-1]:
            clean = re.sub(r'[^A-Za-zА-яЁё]', '', part)
            if clean and clean[0].isalpha():
                initial = clean[0].upper()
                return f"{family} {initial}"

        return family

# ============================================================================
# 🎯 OPTIMIZED DOI PROCESSOR (UPDATED WITH RESUME CAPABILITY)
# ============================================================================

class OptimizedDOIProcessor:
    def __init__(self, cache_manager: SmartCacheManager,
                 delay_manager: AdaptiveDelayManager,
                 data_processor: DataProcessor,
                 failed_tracker: FailedDOITracker):

        self.cache = cache_manager
        self.delay = delay_manager
        self.data_processor = data_processor
        self.failed_tracker = failed_tracker

        self.crossref_client = CrossrefClient(cache_manager, delay_manager)
        self.openalex_client = OpenAlexClient(cache_manager, delay_manager)
        self.ror_client = RORClient(cache_manager)

        self.processed_dois = {}
        self.reference_relationships = defaultdict(list)
        self.citation_relationships = defaultdict(list)

        self.author_affiliation_map = defaultdict(set)
        self.doi_author_map = defaultdict(list)
        self.doi_affiliation_map = defaultdict(set)

        self.stats = {
            'total_processed': 0,
            'successful': 0,
            'failed': 0,
            'cached_hits': 0,
            'api_calls': 0
        }

        # New variables for resume management
        self.current_stage = None
        self.stage_progress = {
            'analyzed': {'processed': [], 'remaining': []},
            'ref': {'processed': [], 'remaining': []},
            'citing': {'processed': [], 'remaining': []}
        }

    def process_doi_batch_with_resume(self, dois: List[str], source_type: str = "analyzed",
                                     original_doi: str = None, fetch_refs: bool = True,
                                     fetch_cites: bool = True, batch_size: int = Config.BATCH_SIZE,
                                     progress_container=None, resume: bool = False,
                                     checkpoint_interval: int = 10) -> Dict[str, Dict]:
        
        # Если возобновляем, загружаем сохраненное состояние
        if resume:
            resume_state = self.load_complete_resume_state()
            if resume_state:
                # Используем восстановленные результаты
                results = resume_state.get('recovered_results', {})
                # Продолжаем с оставшихся DOI
                remaining_dois = self.stage_progress[source_type]['remaining']
                dois = remaining_dois if remaining_dois else dois
        
        results = {}
        
        # Обрабатываем батчами с контрольными точками
        for batch_idx in range(0, len(dois), batch_size):
            batch = dois[batch_idx:batch_idx + batch_size]
            batch_id = batch_idx // batch_size
            
            # Создаем контрольную точку перед обработкой батча
            self._create_checkpoint(source_type, batch_id, batch_idx, len(dois))
            
            # Обрабатываем батч
            batch_results = self._process_batch_with_checkpoints(
                batch, source_type, original_doi, fetch_refs, fetch_cites,
                checkpoint_interval
            )
            
            results.update(batch_results)
            
            # Сохраняем прогресс после каждого батча
            self._save_batch_progress(
                source_type, batch_id, batch_results,
                processed_count=batch_idx + len(batch),
                total_count=len(dois)
            )
            
            # Также сохраняем инкрементальный прогресс для каждого DOI
            for doi, result in batch_results.items():
                self.cache.save_incremental_progress(doi, source_type, result)
            
        # Check if can resume from interrupted point
        if resume and source_type in self.stage_progress:
            if self.stage_progress[source_type]['remaining']:
                # Continue from interrupted point
                dois = self.stage_progress[source_type]['remaining']
                st.info(f"🔄 Resuming {source_type} processing with {len(dois)} remaining DOI")
            else:
                # No saved progress, start from beginning
                self.stage_progress[source_type] = {'processed': [], 'remaining': dois}

        results = {}
        total_batches = (len(dois) + batch_size - 1) // batch_size

        if progress_container:
            status_text = progress_container.text(f"🔧 Processing {len(dois)} DOI (source: {source_type})")
            progress_bar = progress_container.progress(0)
        else:
            status_text = None
            progress_bar = None

        monitor = ProgressMonitor(len(dois), f"Processing {source_type}", progress_bar, status_text)

        try:
            for batch_idx in range(0, len(dois), batch_size):
                batch = dois[batch_idx:batch_idx + batch_size]
                batch_results = self._process_single_batch_with_retry(
                    batch, source_type, original_doi, True, True
                )

                results.update(batch_results)

                # Update progress
                processed_batch = list(batch_results.keys())
                self.stage_progress[source_type]['processed'].extend(processed_batch)
                self.stage_progress[source_type]['remaining'] = dois[batch_idx + batch_size:]
                
                # Save progress to cache
                self.cache.save_progress(
                    source_type,
                    self.stage_progress[source_type]['processed'],
                    self.stage_progress[source_type]['remaining']
                )

                monitor.update(len(batch), 'processed')

                batch_success = sum(1 for r in batch_results.values() if r.get('status') == 'success')

            # Clear saved progress after successful completion
            self.stage_progress[source_type] = {'processed': [], 'remaining': []}
            self.cache.clear_progress()

            monitor.complete()

            successful = sum(1 for r in results.values() if r.get('status') == 'success')
            failed = len(dois) - successful

            self.stats['total_processed'] += len(dois)
            self.stats['successful'] += successful
            self.stats['failed'] += failed

            return results

        except Exception as e:
            # Save progress on exception
            st.warning(f"⚠️ {source_type} processing interrupted: {e}")
            st.info(f"📊 Progress saved. Can resume from interruption point.")
            return results

    def _process_single_batch_with_retry(self, batch: List[str], source_type: str,
                                       original_doi: str, fetch_refs: bool, fetch_cites: bool) -> Dict[str, Dict]:
        """Process DOI batch with retries for empty results"""
        results = {}

        with ThreadPoolExecutor(max_workers=min(Config.MAX_WORKERS, len(batch))) as executor:
            future_to_doi = {}

            for doi in batch:
                future = executor.submit(
                    self._process_single_doi_with_validation,
                    doi, source_type, original_doi, True, True
                )
                future_to_doi[future] = doi

            for future in as_completed(future_to_doi):
                doi = future_to_doi[future]
                try:
                    result = future.result(timeout=60)
                    
                    # Check result for emptiness and retry if needed
                    if self._is_empty_result(result):
                        st.warning(f"⚠️ Empty result for {doi}, retrying...")
                        # Retry without exponential delays
                        result = self._retry_process_single_doi(doi, source_type, original_doi)
                    
                    results[doi] = result
                    
                except Exception as e:
                    self._handle_processing_error(doi, str(e), source_type, original_doi)
                    results[doi] = {
                        'doi': doi,
                        'status': 'failed',
                        'error': f"Processing timeout: {str(e)}"
                    }

        return results

    def _is_empty_result(self, result: Dict) -> bool:
        """Check if result is empty (insufficient data)"""
        if result.get('status') != 'success':
            return False
        
        pub_info = result.get('publication_info', {})
        title = pub_info.get('title', '')
        authors = result.get('authors', [])
        
        # Check main fields for emptiness
        empty_fields = [
            not title or title in ['Title not found', 'Request timeout', 'Network error', 'Retrieval error'],
            not authors,
            not pub_info.get('journal', ''),
            not pub_info.get('year', '')
        ]
        
        # If all main fields empty
        if all(empty_fields):
            return True
        
        return False

    def _retry_process_single_doi(self, doi: str, source_type: str, original_doi: str) -> Dict:
        """Retry processing DOI without exponential delays"""
        try:
            # Save current delay settings
            original_delay = self.delay.current_delay
            
            # Temporarily set basic delay for retry
            self.delay.current_delay = Config.INITIAL_DELAY
            
            result = self._process_single_doi_optimized(
                doi, source_type, original_doi, True, True
            )
            
            validated_result = self._validate_result_before_caching(result, doi, source_type)
            return validated_result
            
            # Restore original delay
            self.delay.current_delay = original_delay
            
            return result
            
        except Exception as e:
            self._handle_processing_error(doi, str(e), source_type, original_doi)
            return {
                'doi': doi,
                'status': 'failed',
                'error': f"Retry processing error: {str(e)}"
            }

    def process_doi_batch(self, dois: List[str], source_type: str = "analyzed",
                         original_doi: str = None, fetch_refs: bool = True,
                         fetch_cites: bool = True, batch_size: int = Config.BATCH_SIZE,
                         progress_container=None) -> Dict[str, Dict]:
        return self.process_doi_batch_with_resume(
            dois, source_type, original_doi, fetch_refs, fetch_cites, 
            batch_size, progress_container, resume=False
        )

    def _process_single_batch(self, batch: List[str], source_type: str,
                             original_doi: str, fetch_refs: bool, fetch_cites: bool) -> Dict[str, Dict]:
        results = {}

        with ThreadPoolExecutor(max_workers=min(Config.MAX_WORKERS, len(batch))) as executor:
            future_to_doi = {}

            for doi in batch:
                future = executor.submit(
                    self._process_single_doi_wrapper,
                    doi, source_type, original_doi, True, True
                )
                future_to_doi[future] = doi

            for future in as_completed(future_to_doi):
                doi = future_to_doi[future]
                try:
                    results[doi] = future.result(timeout=60)
                except Exception as e:
                    self._handle_processing_error(doi, str(e), source_type, original_doi)
                    results[doi] = {
                        'doi': doi,
                        'status': 'failed',
                        'error': f"Processing timeout: {str(e)}"
                    }

        return results

    def _process_single_doi_wrapper(self, doi: str, source_type: str,
                                   original_doi: str, fetch_refs: bool, fetch_cites: bool) -> Dict:
        try:
            return self._process_single_doi_optimized(
                doi, source_type, original_doi, True, True
            )
            validated_result = self._validate_result_before_caching(result, doi, source_type)
            return validated_result
        except Exception as e:
            self._handle_processing_error(doi, str(e), source_type, original_doi)
            return {
                'doi': doi,
                'status': 'failed',
                'error': f"Processing error: {str(e)}"
            }

    def _process_single_doi_with_validation(self, doi: str, source_type: str,
                                          original_doi: str, fetch_refs: bool, fetch_cites: bool) -> Dict:
        """Wrapper for processing with result validation"""
        try:
            result = self._process_single_doi_optimized(
                doi, source_type, original_doi, True, True
            )
            return result
        except Exception as e:
            self._handle_processing_error(doi, str(e), source_type, original_doi)
            return {
                'doi': doi,
                'status': 'failed',
                'error': f"Processing error: {str(e)}"
            }

    def _process_single_doi_optimized(self, doi: str, source_type: str,
                                     original_doi: str, fetch_refs: bool, fetch_cites: bool) -> Dict:

        cache_key = f"full_result:{doi}"
        cached_result = self.cache.get("full_analysis", cache_key)

        if cached_result is not None:
            self.stats['cached_hits'] += 1
            return cached_result

        crossref_data = {}
        openalex_data = {}

        try:
            crossref_data = self.crossref_client.fetch_article(doi)
            openalex_data = self.openalex_client.fetch_article(doi)
        except Exception as e:
            error_msg = f"Data retrieval error: {str(e)}"
            self._handle_processing_error(doi, error_msg, source_type, original_doi)
            return {
                'doi': doi,
                'status': 'failed',
                'error': error_msg
            }

        crossref_error = None
        openalex_error = None

        if isinstance(crossref_data, dict):
            crossref_error = crossref_data.get('error')
        if isinstance(openalex_data, dict):
            openalex_error = openalex_data.get('error')

        if crossref_error and openalex_error:
            error_msg = f"API errors: Crossref - {crossref_error}, OpenAlex - {openalex_error}"
            self._handle_processing_error(doi, error_msg, source_type, original_doi)
            return {
                'doi': doi,
                'status': 'failed',
                'error': error_msg
            }

        crossref_data = crossref_data if isinstance(crossref_data, dict) else {}
        openalex_data = openalex_data if isinstance(openalex_data, dict) else {}

        references = []
        try:
            refs = self.crossref_client.fetch_references(doi)
            references = refs if isinstance(refs, list) else []

            if references:
                self.reference_relationships[doi] = references
        except Exception as e:
            st.warning(f"⚠️ Error fetching references for {doi}: {e}")

        citations = []
        try:
            # IMPORTANT CHANGE: Different citation collection logic depending on article type
            if source_type == "analyzed":
                # For analyzed articles: collect ALL citations through new logic
                cites_openalex = self.openalex_client.fetch_all_citations_for_analyzed_article(doi)

                # Also get citations from Crossref for data completeness
                cites_crossref = self.crossref_client.fetch_citations(doi)
                cites_crossref = cites_crossref if isinstance(cites_crossref, list) else []

                citations = list(set(cites_openalex + cites_crossref))

                if citations:
                    self.citation_relationships[doi] = citations

            else:
                # For reference and citing articles: use old logic (only up to 2000)
                cites_openalex = self.openalex_client.fetch_citations(doi)
                cites_crossref = self.crossref_client.fetch_citations(doi)

                cites_openalex = cites_openalex if isinstance(cites_openalex, list) else []
                cites_crossref = cites_crossref if isinstance(cites_crossref, list) else []

                citations = list(set(cites_openalex + cites_crossref))

                if citations:
                    self.citation_relationships[doi] = citations
        except Exception as e:
            st.warning(f"⚠️ Error fetching citations for {doi}: {e}")
            # If error collecting citations for analyzed article,
            # try to use old logic as fallback
            if source_type == "analyzed":
                try:
                    cites_openalex = self.openalex_client.fetch_citations(doi)
                    cites_crossref = self.crossref_client.fetch_citations(doi)
                    cites_openalex = cites_openalex if isinstance(cites_openalex, list) else []
                    cites_crossref = cites_crossref if isinstance(cites_crossref, list) else []
                    citations = list(set(cites_openalex + cites_crossref))

                    if citations:
                        self.citation_relationships[doi] = citations
                except Exception as e2:
                    st.warning(f"❌ Fallback also failed for {doi}: {e2}")

        result = self.data_processor.extract_article_info(
            crossref_data, openalex_data, doi, references, citations
        )

        if result.get('status') == 'success':
            for author in result.get('authors', []):
                author_name = author.get('name', '')
                if author_name:
                    self.doi_author_map[doi].append(author_name)
                    for affiliation in author.get('affiliation', []):
                        if affiliation:
                            self.author_affiliation_map[author_name].add(affiliation)
                            self.doi_affiliation_map[doi].add(affiliation)

        validated_result = self._validate_result_before_caching(result, doi, source_type)
        result = validated_result
                                         
        if result.get('status') == 'success':
            self.stats['successful'] += 1

            self.cache.set("full_analysis", cache_key, result, category="full_analysis")

            self.cache.update_popularity(doi)
        else:
            self.stats['failed'] += 1

        self.stats['api_calls'] += 2

        return result

    def _handle_processing_error(self, doi: str, error: str, source_type: str, original_doi: str):

        related_dois = []
        if original_doi:
            related_dois.append(original_doi)

        self.failed_tracker.add_failed_doi(
            doi=doi,
            error=error,
            source_type=source_type,
            related_dois=related_dois,
            original_doi=original_doi
        )

        self.cache.mark_as_failed("full_analysis", doi, error)

    def _validate_result_before_caching(self, result: Dict, doi: str, source_type: str) -> Dict:
        """Валидация результата перед кэшированием"""
        try:
            if result is None:
                raise ValueError("Result is None")
                
            if not isinstance(result, dict):
                raise ValueError(f"Result is not dict, type: {type(result)}")
            
            # Проверяем обязательные поля
            if 'doi' not in result:
                result['doi'] = doi
                
            if 'status' not in result:
                result['status'] = 'success' if result.get('publication_info') else 'failed'
                
            # Проверяем публикационную информацию
            if 'publication_info' not in result:
                result['publication_info'] = {}
            elif result['publication_info'] is None:
                result['publication_info'] = {}
                
            # Проверяем авторов
            if 'authors' not in result:
                result['authors'] = []
            elif result['authors'] is None:
                result['authors'] = []
                
            # Проверяем страны
            if 'countries' not in result:
                result['countries'] = []
            elif result['countries'] is None:
                result['countries'] = []
                
            # Проверяем темы
            if 'topics_info' not in result:
                result['topics_info'] = {}
            elif result['topics_info'] is None:
                result['topics_info'] = {}
                
            # Проверяем ORCID
            if 'orcid_urls' not in result:
                result['orcid_urls'] = []
            elif result['orcid_urls'] is None:
                result['orcid_urls'] = []
                
            # Проверяем ссылки и цитирования
            if 'references' not in result:
                result['references'] = []
            elif result['references'] is None:
                result['references'] = []
                
            if 'citations' not in result:
                result['citations'] = []
            elif result['citations'] is None:
                result['citations'] = []
                
            return result
        
        except Exception as e:
            st.warning(f"⚠️ Validation error for {doi} ({source_type}): {str(e)}")
            # Возвращаем безопасный результат
            return {
                'doi': doi,
                'status': 'failed',
                'error': f"Validation error: {str(e)}",
                'publication_info': {},
                'authors': [],
                'countries': [],
                'topics_info': {},
                'orcid_urls': [],
                'references': [],
                'citations': [],
                'references_count': 0,
                'pages_formatted': '',
                'quick_insights': {}
            }

    def collect_all_references(self, results: Dict[str, Dict]) -> List[str]:
        all_refs = []

        for doi, result in results.items():
            if result.get('status') == 'success':
                refs = result.get('references', [])
                if refs:
                    all_refs.extend(refs)

        for doi, result in results.items():
            if result.get('status') == 'success':
                refs = result.get('references', [])
                if refs:
                    for ref_doi in refs:
                        if ref_doi not in self.reference_relationships:
                            self.reference_relationships[ref_doi] = []
                        if doi not in self.reference_relationships[ref_doi]:
                            self.reference_relationships[ref_doi].append(doi)

        return all_refs

    def collect_all_citations(self, results: Dict[str, Dict]) -> List[str]:
        all_cites = []

        for doi, result in results.items():
            if result.get('status') == 'success':
                cites = result.get('citations', [])
                if cites:
                    all_cites.extend(cites)

        return all_cites

    def get_relationships(self) -> Dict[str, Any]:
        return {
            'reference_relationships': dict(self.reference_relationships),
            'citation_relationships': dict(self.citation_relationships),
            'total_relationships': len(self.reference_relationships) + len(self.citation_relationships)
        }

    def get_insights_data(self) -> Dict[str, Any]:
        return {
            'author_affiliation_map': dict(self.author_affiliation_map),
            'doi_author_map': dict(self.doi_author_map),
            'doi_affiliation_map': dict(self.doi_affiliation_map)
        }

    def get_stats(self) -> Dict[str, Any]:
        return {
            'total_processed': self.stats['total_processed'],
            'successful': self.stats['successful'],
            'failed': self.stats['failed'],
            'cached_hits': self.stats['cached_hits'],
            'api_calls': self.stats['api_calls'],
            'cache_efficiency': round((self.stats['cached_hits'] / max(1, self.stats['total_processed'])) * 100, 1),
            'success_rate': round((self.stats['successful'] / max(1, self.stats['total_processed'])) * 100, 1)
        }

    def retry_failed_dois(self, failed_tracker: FailedDOITracker, max_retries: int = 1) -> Dict[str, Dict]:
        retry_results = {}

        rate_limit_dois = []
        for doi, info in failed_tracker.failed_dois.items():
            if 'Rate limit exceeded' in info.get('error', ''):
                rate_limit_dois.append(doi)

        if not rate_limit_dois:
            return retry_results

        original_delay = self.delay.current_delay
        self.delay.current_delay = min(Config.MAX_DELAY, original_delay * 1.5)

        retry_results = self.process_doi_batch(
            rate_limit_dois, "retry", None, True, True, Config.BATCH_SIZE
        )

        self.delay.current_delay = original_delay

        successful_retries = sum(1 for r in retry_results.values() if r.get('status') == 'success')

        return retry_results

    def load_complete_resume_state(self):
        """Полная загрузка состояния для возобновления"""
        # Загружаем основной прогресс
        stage, processed, remaining = self.cache.load_progress()
        
        if not stage:
            return None
        
        # Загружаем инкрементальный прогресс из кэша
        incremental_data = self._load_incremental_progress(stage)
        
        # Загружаем данные батчей
        batch_data = self._load_batch_progress(stage)
        
        # Восстанавливаем обработанные DOI
        recovered_results = {}
        if incremental_data:
            for doi, data in incremental_data.items():
                if data.get('status') == 'completed':
                    recovered_results[doi] = data.get('data', {})
        
        # Обновляем состояние процессора
        self.current_stage = stage
        self.stage_progress[stage]['processed'] = processed
        self.stage_progress[stage]['remaining'] = remaining
        self.stage_progress[stage]['recovered_results'] = recovered_results
        self.stage_progress[stage]['batch_data'] = batch_data
        
        return {
            'stage': stage,
            'processed_count': len(processed),
            'remaining_count': len(remaining),
            'recovered_results': len(recovered_results),
            'batch_progress': batch_data
        }
    
# ============================================================================
# 📊 TITLE KEYWORDS ANALYZER (WITH LEMMATIZATION)
# ============================================================================

class TitleKeywordsAnalyzer:
    def __init__(self):
        # Initialize stopwords and lemmatizer
        try:
            import nltk
            from nltk.corpus import stopwords
            from nltk.stem import WordNetLemmatizer
            
            # Load necessary NLTK resources
            try:
                nltk.download('wordnet', quiet=True)
                nltk.download('omw-eng', quiet=True)
                nltk.download('stopwords', quiet=True)
                nltk.download('punkt', quiet=True)
            except:
                pass
            
            self.stop_words = set(stopwords.words('english'))
            self.lemmatizer = WordNetLemmatizer()
            
            # Rules for special cases
            self.irregular_plurals = {
                'analyses': 'analysis',
                'axes': 'axis',
                'bases': 'basis',
                'crises': 'crisis',
                'criteria': 'criterion',
                'data': 'datum',
                'diagnoses': 'diagnosis',
                'ellipses': 'ellipsis',
                'emphases': 'emphasis',
                'genera': 'genus',
                'hypotheses': 'hypothesis',
                'indices': 'index',
                'media': 'medium',
                'memoranda': 'memorandum',
                'parentheses': 'parenthesis',
                'phenomena': 'phenomenon',
                'prognoses': 'prognosis',
                'radii': 'radius',
                'stimuli': 'stimulus',
                'syntheses': 'synthesis',
                'theses': 'thesis',
                'vertebrae': 'vertebra',
                # Add scientific terms
                'oxides': 'oxide',
                'composites': 'composite',
                'applications': 'application',
                'materials': 'material',
                'methods': 'method',
                'systems': 'system',
                'techniques': 'technique',
                'properties': 'property',
                'structures': 'structure',
                'devices': 'device',
                'processes': 'process',
                'mechanisms': 'mechanism',
                'models': 'model',
                'approaches': 'approach',
                'frameworks': 'framework',
                'strategies': 'strategy',
                'solutions': 'solution',
                'technologies': 'technology',
                'materials': 'material',
                'nanoparticles': 'nanoparticle',
                'nanostructures': 'nanostructure',
                'polymers': 'polymer',
                'composites': 'composite',
                'ceramics': 'ceramic',
                'alloys': 'alloy',
                'coatings': 'coating',
                'films': 'film',
                'layers': 'layer',
                'interfaces': 'interface',
                'surfaces': 'surface',
                'catalysts': 'catalyst',
                'sensors': 'sensor',
                'actuators': 'actuator',
                'transistors': 'transistor',
                'diodes': 'diode',
                'circuits': 'circuit',
                'networks': 'network',
                'algorithms': 'algorithm',
                'protocols': 'protocol',
                'databases': 'database',
                'architectures': 'architecture',
                'platforms': 'platform',
                'environments': 'environment',
                'simulations': 'simulation',
                'experiments': 'experiment',
                'measurements': 'measurement',
                'observations': 'observation',
                'analyses': 'analysis',
                'evaluations': 'evaluation',
                'assessments': 'assessment',
                'comparisons': 'comparison',
                'classifications': 'classification',
                'predictions': 'prediction',
                'optimizations': 'optimization',
                'characterizations': 'characterization',
                'syntheses': 'synthesis',
                'fabrications': 'fabrication',
                'preparations': 'preparation',
                'treatments': 'treatment',
                'modifications': 'modification',
                'enhancements': 'enhancement',
                'improvements': 'improvement',
                'developments': 'development',
                'innovations': 'innovation',
                'discoveries': 'discovery',
                'inventions': 'invention',
                'applications': 'application',
                'implementations': 'implementation',
                'utilizations': 'utilization',
                'integrations': 'integration',
                'combinations': 'combination',
                'interactions': 'interaction',
                'relationships': 'relationship',
                'dependencies': 'dependency',
                'correlations': 'correlation',
                'associations': 'association',
                'connections': 'connection',
                'communications': 'communication',
                'collaborations': 'collaboration',
                'cooperations': 'cooperation',
                'competitions': 'competition',
                'conflicts': 'conflict',
                'challenges': 'challenge',
                'problems': 'problem',
                'solutions': 'solution',
                'alternatives': 'alternative',
                'options': 'option',
                'variants': 'variant',
                'versions': 'version',
                'editions': 'edition',
                'releases': 'release',
                'updates': 'update',
                'revisions': 'revision',
                'modifications': 'modification',
                'adaptations': 'adaptation',
                'customizations': 'customization',
                'personalizations': 'personalization',
                'localizations': 'localization',
                'internationalizations': 'internationalization',
                'standardizations': 'standardization',
                'normalizations': 'normalization',
                'optimizations': 'optimization',
                'maximizations': 'maximization',
                'minimizations': 'minimization',
                'reductions': 'reduction',
                'increases': 'increase',
                'improvements': 'improvement',
                'enhancements': 'enhancement',
                'advancements': 'advancement',
                'progresses': 'progress',
                'developments': 'development',
                'evolutions': 'evolution',
                'revolutions': 'revolution',
                'transformations': 'transformation',
                'changes': 'change',
                'variations': 'variation',
                'fluctuations': 'fluctuation',
                'oscillations': 'oscillation',
                'vibrations': 'vibration',
                'rotations': 'rotation',
                'translations': 'translation',
                'movements': 'movement',
                'motions': 'motion',
                'dynamics': 'dynamic',
                'kinematics': 'kinematic',
                'mechanics': 'mechanic',
                'thermodynamics': 'thermodynamic',
                'electrodynamics': 'electrodynamic',
                'hydrodynamics': 'hydrodynamic',
                'aerodynamics': 'aerodynamic',
                'biomechanics': 'biomechanic',
                'geomechanics': 'geomechanic',
                'chemomechanics': 'chemomechanic',
                'tribology': 'tribology',
                'rheology': 'rheology',
                'viscoelasticity': 'viscoelastic',
                'plasticity': 'plastic',
                'elasticity': 'elastic',
                'viscosity': 'viscous',
                'conductivity': 'conductive',
                'resistivity': 'resistive',
                'permeability': 'permeable',
                'porosity': 'porous',
                'density': 'dense',
                'hardness': 'hard',
                'stiffness': 'stiff',
                'strength': 'strong',
                'toughness': 'tough',
                'brittleness': 'brittle',
                'ductility': 'ductile',
                'malleability': 'malleable',
                'flexibility': 'flexible',
                'rigidity': 'rigid',
                'stability': 'stable',
                'instability': 'unstable',
                'reliability': 'reliable',
                'durability': 'durable',
                'sustainability': 'sustainable',
                'efficiency': 'efficient',
                'effectiveness': 'effective',
                'performance': 'perform',
                'productivity': 'productive',
                'quality': 'qualitative',
                'quantity': 'quantitative',
                'accuracy': 'accurate',
                'precision': 'precise',
                'reliability': 'reliable',
                'validity': 'valid',
                'reproducibility': 'reproducible',
                'repeatability': 'repeatable',
                'consistency': 'consistent',
                'homogeneity': 'homogeneous',
                'heterogeneity': 'heterogeneous',
                'isotropy': 'isotropic',
                'anisotropy': 'anisotropic',
                'symmetry': 'symmetric',
                'asymmetry': 'asymmetric',
                'regularity': 'regular',
                'irregularity': 'irregular',
                'periodicity': 'periodic',
                'aperiodicity': 'aperiodic',
                'randomness': 'random',
                'determinism': 'deterministic',
                'stochasticity': 'stochastic',
                'probability': 'probable',
                'statistics': 'statistic',
                'distributions': 'distribution',
                'functions': 'function',
                'equations': 'equation',
                'formulas': 'formula',
                'theorems': 'theorem',
                'lemmas': 'lemma',
                'corollaries': 'corollary',
                'proofs': 'proof',
                'demonstrations': 'demonstration',
                'verifications': 'verification',
                'validations': 'validation',
                'confirmations': 'confirmation',
                'tests': 'test',
                'experiments': 'experiment',
                'trials': 'trial',
                'studies': 'study',
                'investigations': 'investigation',
                'examinations': 'examination',
                'inspections': 'inspection',
                'audits': 'audit',
                'reviews': 'review',
                'surveys': 'survey',
                'polls': 'poll',
                'questionnaires': 'questionnaire',
                'interviews': 'interview',
                'observations': 'observation',
                'measurements': 'measurement',
                'calculations': 'calculation',
                'computations': 'computation',
                'simulations': 'simulation',
                'modelings': 'modeling',
                'analyses': 'analysis',
                'syntheses': 'synthesis',
                'evaluations': 'evaluation',
                'assessments': 'assessment',
                'appraisals': 'appraisal',
                'estimations': 'estimation',
                'approximations': 'approximation',
                'predictions': 'prediction',
                'forecasts': 'forecast',
                'projections': 'projection',
                'extrapolations': 'extrapolation',
                'interpolations': 'interpolation',
                'regressions': 'regression',
                'correlations': 'correlation',
                'classifications': 'classification',
                'clusters': 'cluster',
                'segments': 'segment',
                'groups': 'group',
                'categories': 'category',
                'types': 'type',
                'classes': 'class',
                'kinds': 'kind',
                'sorts': 'sort',
                'varieties': 'variety',
                'forms': 'form',
                'shapes': 'shape',
                'sizes': 'size',
                'dimensions': 'dimension',
                'volumes': 'volume',
                'areas': 'area',
                'lengths': 'length',
                'widths': 'width',
                'heights': 'height',
                'depths': 'depth',
                'thicknesses': 'thickness',
                'diameters': 'diameter',
                'radii': 'radius',
                'circumferences': 'circumference',
                'perimeters': 'perimeter',
                'surfaces': 'surface',
                'interfaces': 'interface',
                'boundaries': 'boundary',
                'edges': 'edge',
                'corners': 'corner',
                'vertices': 'vertex',
                'nodes': 'node',
                'points': 'point',
                'lines': 'line',
                'curves': 'curve',
                'planes': 'plane',
                'spaces': 'space',
                'regions': 'region',
                'zones': 'zone',
                'sectors': 'sector',
                'segments': 'segment',
                'parts': 'part',
                'components': 'component',
                'elements': 'element',
                'units': 'unit',
                'modules': 'module',
                'blocks': 'block',
                'pieces': 'piece',
                'fragments': 'fragment',
                'particles': 'particle',
                'atoms': 'atom',
                'molecules': 'molecule',
                'ions': 'ion',
                'electrons': 'electron',
                'protons': 'proton',
                'neutrons': 'neutron',
                'photons': 'photon',
                'quarks': 'quark',
                'leptons': 'lepton',
                'bosons': 'boson',
                'fermions': 'fermion',
                'hadrons': 'hadron',
                'mesons': 'meson',
                'baryons': 'baryon',
                'nuclei': 'nucleus',
                'isotopes': 'isotope',
                'elements': 'element',
                'compounds': 'compound',
                'mixtures': 'mixture',
                'solutions': 'solution',
                'suspensions': 'suspension',
                'colloids': 'colloid',
                'emulsions': 'emulsion',
                'foams': 'foam',
                'gels': 'gel',
                'solids': 'solid',
                'liquids': 'liquid',
                'gases': 'gas',
                'plasmas': 'plasma',
                'crystals': 'crystal',
                'amorphous': 'amorphous',
                'polymers': 'polymer',
                'monomers': 'monomer',
                'oligomers': 'oligomer',
                'copolymers': 'copolymer',
                'homopolymers': 'homopolymer',
                'biopolymers': 'biopolymer',
                'proteins': 'protein',
                'enzymes': 'enzyme',
                'antibodies': 'antibody',
                'antigens': 'antigen',
                'vaccines': 'vaccine',
                'drugs': 'drug',
                'medicines': 'medicine',
                'therapies': 'therapy',
                'treatments': 'treatment',
                'diagnoses': 'diagnosis',
                'prognoses': 'prognosis',
                'symptoms': 'symptom',
                'diseases': 'disease',
                'disorders': 'disorder',
                'conditions': 'condition',
                'syndromes': 'syndrome',
                'infections': 'infection',
                'inflammations': 'inflammation',
                'tumors': 'tumor',
                'cancers': 'cancer',
                'metastases': 'metastasis',
                'remissions': 'remission',
                'recurrences': 'recurrence',
                'survivals': 'survival',
                'mortality': 'mortal',
                'morbidity': 'morbid',
                'epidemiology': 'epidemiologic',
                'pathology': 'pathologic',
                'physiology': 'physiologic',
                'anatomy': 'anatomic',
                'histology': 'histologic',
                'cytology': 'cytologic',
                'genetics': 'genetic',
                'genomics': 'genomic',
                'proteomics': 'proteomic',
                'metabolomics': 'metabolomic',
                'transcriptomics': 'transcriptomic',
                'epigenetics': 'epigenetic',
                'bioinformatics': 'bioinformatic',
                'biotechnology': 'biotechnologic',
                'nanotechnology': 'nanotechnologic',
                'microtechnology': 'microtechnologic',
                'microfabrication': 'microfabricate',
                'nanofabrication': 'nanofabricate',
                'lithography': 'lithographic',
                'photolithography': 'photolithographic',
                'electron-beam': 'electron-beam',
                'ion-beam': 'ion-beam',
                'focused-ion-beam': 'focused-ion-beam',
                'atomic-force': 'atomic-force',
                'scanning-tunneling': 'scanning-tunneling',
                'transmission-electron': 'transmission-electron',
                'scanning-electron': 'scanning-electron',
                'optical': 'optical',
                'confocal': 'confocal',
                'fluorescence': 'fluorescent',
                'phosphorescence': 'phosphorescent',
                'luminescence': 'luminescent',
                'chemiluminescence': 'chemiluminescent',
                'bioluminescence': 'bioluminescent',
                'electroluminescence': 'electroluminescent',
                'photoluminescence': 'photoluminescent',
                'cathodoluminescence': 'cathodoluminescent',
                'thermoluminescence': 'thermoluminescent',
                'radioluminescence': 'radioluminescent',
                'sonoluminescence': 'sonoluminescent',
                'triboluminescence': 'triboluminescent',
                'crystalloluminescence': 'crystalloluminescent',
                'electroluminescence': 'electroluminescent',
                'magnetoluminescence': 'magnetoluminescent',
            }
            
            # Suffixes that need conversion
            self.suffix_replacements = {
                'ies': 'y',
                'es': '',
                's': '',
                'ed': '',
                'ing': '',
                'ly': '',
                'ally': 'al',
                'ically': 'ic',
                'ization': 'ize',
                'isation': 'ise',
                'ment': '',
                'ness': '',
                'ity': '',
                'ty': '',
                'ic': '',
                'ical': '',
                'ive': '',
                'ous': '',
                'ful': '',
                'less': '',
                'est': '',
                'er': '',
                'ors': 'or',
                'ors': 'or',
                'ings': 'ing',
                'ments': 'ment',
            }
            
        except:
            # Fallback if nltk not available
            self.stop_words = {'a', 'an', 'the', 'and', 'or', 'but', 'in', 'on', 'at', 'to', 'for', 'of', 'with', 'by'}
            self.lemmatizer = None
            self.irregular_plurals = {}
            self.suffix_replacements = {}
        
        # Scientific stopwords (already lemmatized)
        self.scientific_stopwords = {
            'activate', 'adapt', 'advance', 'analyze', 'apply',
            'approach', 'architect', 'artificial', 'assess',
            'base', 'behave', 'capacity', 'characterize',
            'coat', 'compare', 'compute', 'composite',
            'control', 'cycle', 'damage', 'data', 'density', 'design',
            'detect', 'develop', 'device', 'diagnose', 'discover',
            'dynamic', 'economic', 'effect', 'efficacy',
            'efficient', 'energy', 'engineer', 'enhance', 'environment',
            'evaluate', 'experiment', 'explore', 'factor', 'fail',
            'fabricate', 'field', 'film', 'flow', 'framework', 'frequency',
            'function', 'grow', 'high', 'impact', 'improve',
            'induce', 'influence', 'inform', 'innovate', 'intelligent',
            'interact', 'interface', 'investigate', 'know',
            'layer', 'learn', 'magnetic', 'manage', 'material',
            'measure', 'mechanism', 'medical',
            'method', 'model', 'modify', 'modulate',
            'molecule', 'monitor', 'motion', 'nanoparticle',
            'nanostructure', 'network', 'neural', 'new', 'nonlinear',
            'novel', 'numerical', 'optical', 'optimize', 'pattern', 'perform',
            'phenomenon', 'potential', 'power', 'predict', 'prepare', 'process',
            'produce', 'progress', 'property', 'quality', 'regulate', 'relate',
            'reliable', 'remote', 'repair', 'research', 'resist', 'respond',
            'review', 'risk', 'role', 'safe', 'sample', 'scale', 'screen',
            'separate', 'signal', 'simulate', 'specific', 'stable', 'state',
            'store', 'strain', 'strength', 'stress', 'structure', 'study',
            'sustain', 'synergy', 'synthesize', 'system', 'target',
            'technique', 'technology', 'test', 'theoretical', 'therapy',
            'thermal', 'tissue', 'tolerate', 'toxic', 'transform', 'transition',
            'transmit', 'transport', 'type', 'understand', 'use', 'validate',
            'value', 'vary', 'virtual', 'waste', 'wave',
            # Add scientific stopwords that frequently appear
            'application', 'approach', 'assessment', 'behavior', 'capability',
            'characterization', 'comparison', 'concept', 'condition', 'configuration',
            'construction', 'contribution', 'demonstration', 'description', 'detection',
            'determination', 'development', 'effectiveness', 'efficiency', 'evaluation',
            'examination', 'experimentation', 'explanation', 'exploration', 'fabrication',
            'formation', 'implementation', 'improvement', 'indication', 'investigation',
            'management', 'manufacture', 'measurement', 'modification', 'observation',
            'operation', 'optimization', 'performance', 'preparation', 'presentation',
            'production', 'realization', 'recognition', 'regulation', 'representation',
            'simulation', 'solution', 'specification', 'synthesis', 'transformation',
            'treatment', 'utilization', 'validation', 'verification'
        }
    
    def _get_lemma(self, word: str) -> str:
        """Get word lemma considering special rules"""
        if not word or len(word) < 3:
            return word
        
        # Convert to lowercase for processing
        lower_word = word.lower()
        
        # Check irregular plurals FIRST
        if lower_word in self.irregular_plurals:
            return self.irregular_plurals[lower_word]
        
        # Check regular plurals
        # If word ends with 's' or 'es' but not 'ss' or 'us'
        if lower_word.endswith('s') and not (lower_word.endswith('ss') or lower_word.endswith('us')):
            # Try to remove 's' or 'es'
            if lower_word.endswith('es') and len(lower_word) > 2:
                base_word = lower_word[:-2]
                # Check that after removing 'es' word not too short
                if len(base_word) >= 3:
                    return base_word
            elif len(lower_word) > 1:
                base_word = lower_word[:-1]
                # Check that after removing 's' word not too short
                if len(base_word) >= 3:
                    return base_word
        
        # Use lemmatizer if available
        if self.lemmatizer:
            # Try different parts of speech
            for pos in ['n', 'v', 'a', 'r']:  # noun, verb, adjective, adverb
                lemma = self.lemmatizer.lemmatize(lower_word, pos=pos)
                if lemma != lower_word:
                    return lemma
        
        # Apply suffix rules in reverse order (long to short)
        sorted_suffixes = sorted(self.suffix_replacements.keys(), key=len, reverse=True)
        for suffix in sorted_suffixes:
            if lower_word.endswith(suffix) and len(lower_word) > len(suffix) + 2:
                replacement = self.suffix_replacements[suffix]
                base = lower_word[:-len(suffix)] + replacement
                # Check result not too short
                if len(base) >= 3:
                    # Also check base doesn't end with double consonant
                    if len(base) >= 4 and base[-1] == base[-2]:
                        base = base[:-1]
                    return base
        
        return lower_word
    
    def _get_base_form(self, word: str) -> str:
        """Get base word form with aggressive lemmatization"""
        lemma = self._get_lemma(word)
        
        # Additional rules for scientific terms
        if lemma.endswith('isation'):
            return lemma[:-7] + 'ize'
        elif lemma.endswith('ization'):
            return lemma[:-7] + 'ize'
        elif lemma.endswith('ication'):
            return lemma[:-7] + 'y'
        elif lemma.endswith('ation'):
            return lemma[:-5] + 'e'
        elif lemma.endswith('ition'):
            return lemma[:-5] + 'e'
        elif lemma.endswith('ution'):
            return lemma[:-5] + 'e'
        elif lemma.endswith('ment'):
            return lemma[:-4]
        elif lemma.endswith('ness'):
            return lemma[:-4]
        elif lemma.endswith('ity'):
            return lemma[:-3] + 'e'
        elif lemma.endswith('ty'):
            base = lemma[:-2]
            if base.endswith('i'):
                return base[:-1] + 'y'
            return base
        elif lemma.endswith('ic'):
            return lemma[:-2] + 'y'
        elif lemma.endswith('al'):
            return lemma[:-2]
        elif lemma.endswith('ive'):
            return lemma[:-3] + 'e'
        elif lemma.endswith('ous'):
            return lemma[:-3]
        
        return lemma
    
    def preprocess_content_words(self, text: str) -> List[Dict]:
        """Clean and normalize content words, return dictionaries with lemmas and forms"""
        if not text or text in ['Title not found', 'Request timeout', 'Network error', 'Retrieval error']:
            return []

        text = text.lower()
        text = re.sub(r'[^a-zA-Z\s-]', ' ', text)
        text = re.sub(r'\s+', ' ', text).strip()

        words = text.split()
        content_words = []

        for word in words:
            # EXCLUDE word "sub"
            if word == 'sub':
                continue
            if '-' in word:
                continue
            if len(word) > 2 and word not in self.stop_words:
                lemma = self._get_base_form(word)
                if lemma not in self.scientific_stopwords:
                    content_words.append({
                        'original': word,
                        'lemma': lemma,
                        'type': 'content'
                    })

        return content_words

    def extract_compound_words(self, text: str) -> List[Dict]:
        """Extract hyphenated compound words"""
        if not text or text in ['Title not found', 'Request timeout', 'Network error', 'Retrieval error']:
            return []

        text = text.lower()
        compound_words = re.findall(r'\b[a-z]{2,}-[a-z]{2,}(?:-[a-z]{2,})*\b', text)

        compounds = []
        for word in compound_words:
            parts = word.split('-')
            if not any(part in self.stop_words for part in parts):
                # For compound words lemmatize each part
                lemmatized_parts = []
                for part in parts:
                    lemma = self._get_base_form(part)
                    lemmatized_parts.append(lemma)
                
                compounds.append({
                    'original': word,
                    'lemma': '-'.join(lemmatized_parts),
                    'type': 'compound'
                })

        return compounds

    def extract_scientific_stopwords(self, text: str) -> List[Dict]:
        """Extract scientific stopwords"""
        if not text or text in ['Title not found', 'Request timeout', 'Network error', 'Retrieval error']:
            return []

        text = text.lower()
        text = re.sub(r'[^a-zA-Z\s]', ' ', text)
        text = re.sub(r'\s+', ' ', text).strip()

        words = text.split()
        scientific_words = []

        for word in words:
            if len(word) > 2:
                lemma = self._get_base_form(word)
                if lemma in self.scientific_stopwords:
                    scientific_words.append({
                        'original': word,
                        'lemma': lemma,
                        'type': 'scientific'
                    })

        return scientific_words

    def analyze_titles(self, analyzed_titles: List[str], reference_titles: List[str], citing_titles: List[str]) -> dict:
        """Analyze keywords in analyzed, reference and citing article titles"""
        
        # Analyze analyzed articles
        analyzed_words = []
        valid_analyzed_titles = [t for t in analyzed_titles if t and t not in ['Title not found', 'Request timeout', 'Network error', 'Retrieval error']]
        
        for title in valid_analyzed_titles:
            analyzed_words.extend(self.preprocess_content_words(title))
            analyzed_words.extend(self.extract_compound_words(title))
            analyzed_words.extend(self.extract_scientific_stopwords(title))
        
        # Analyze reference articles
        reference_words = []
        valid_reference_titles = [t for t in reference_titles if t and t not in ['Title not found', 'Request timeout', 'Network error', 'Retrieval error']]
        
        for title in valid_reference_titles:
            reference_words.extend(self.preprocess_content_words(title))
            reference_words.extend(self.extract_compound_words(title))
            reference_words.extend(self.extract_scientific_stopwords(title))
        
        # Analyze citing articles
        citing_words = []
        valid_citing_titles = [t for t in citing_titles if t and t not in ['Title not found', 'Request timeout', 'Network error', 'Retrieval error']]
        
        for title in valid_citing_titles:
            citing_words.extend(self.preprocess_content_words(title))
            citing_words.extend(self.extract_compound_words(title))
            citing_words.extend(self.extract_scientific_stopwords(title))
        
        # Create aggregated data by lemmas
        def aggregate_by_lemma(word_list):
            lemma_dict = {}
            for word_info in word_list:
                lemma = word_info['lemma']
                original = word_info['original']
                
                # Exclude too short lemmas
                if len(lemma) < 3:
                    continue
                    
                if lemma not in lemma_dict:
                    lemma_dict[lemma] = {
                        'lemma': lemma,
                        'type': word_info['type'],
                        'variants': Counter(),
                        'count': 0
                    }
                
                lemma_dict[lemma]['variants'][original] += 1
                lemma_dict[lemma]['count'] += 1
            
            return lemma_dict
        
        analyzed_aggregated = aggregate_by_lemma(analyzed_words)
        reference_aggregated = aggregate_by_lemma(reference_words)
        citing_aggregated = aggregate_by_lemma(citing_words)
        
        # Merge similar lemmas (e.g., "composite" and "composites")
        def merge_similar_lemmas(lemma_dict):
            # Create list for removal after merging
            to_remove = set()
            
            lemmas = list(lemma_dict.keys())
            for i in range(len(lemmas)):
                lemma1 = lemmas[i]
                if lemma1 in to_remove:
                    continue
                    
                for j in range(i+1, len(lemmas)):
                    lemma2 = lemmas[j]
                    if lemma2 in to_remove:
                        continue
                    
                    # Check if lemmas are similar
                    if self._are_similar_lemmas(lemma1, lemma2):
                        # Merge into lemma1
                        lemma_dict[lemma1]['count'] += lemma_dict[lemma2]['count']
                        for variant, count in lemma_dict[lemma2]['variants'].items():
                            lemma_dict[lemma1]['variants'][variant] += count
                        
                        to_remove.add(lemma2)
            
            # Remove merged lemmas
            for lemma in to_remove:
                if lemma in lemma_dict:
                    del lemma_dict[lemma]
            
            return lemma_dict
        
        analyzed_aggregated = merge_similar_lemmas(analyzed_aggregated)
        reference_aggregated = merge_similar_lemmas(reference_aggregated)
        citing_aggregated = merge_similar_lemmas(citing_aggregated)
        
        # Get top 100 for each type
        def get_top_100(aggregated_dict):
            items = list(aggregated_dict.values())
            items.sort(key=lambda x: x['count'], reverse=True)
            return items[:100]
        
        top_100_analyzed = get_top_100(analyzed_aggregated)
        top_100_reference = get_top_100(reference_aggregated)
        top_100_citing = get_top_100(citing_aggregated)
        
        return {
            'analyzed': {
                'words': top_100_analyzed,
                'total_titles': len(valid_analyzed_titles)
            },
            'reference': {
                'words': top_100_reference,
                'total_titles': len(valid_reference_titles)
            },
            'citing': {
                'words': top_100_citing,
                'total_titles': len(valid_citing_titles)
            }
        }
    
    def _are_similar_lemmas(self, lemma1: str, lemma2: str) -> bool:
        """Check if lemmas are similar (e.g., singular/plural)"""
        if lemma1 == lemma2:
            return True
        
        # Check if they are forms of the same word
        # Example: "composite" and "composites"
        if lemma1.endswith('s') and lemma1[:-1] == lemma2:
            return True
        if lemma2.endswith('s') and lemma2[:-1] == lemma1:
            return True
        
        # Check if they are forms with different suffixes
        # Example: "characterization" and "characterize"
        common_prefix = self._get_common_prefix(lemma1, lemma2)
        if len(common_prefix) >= 5:  # If common prefix long enough
            # Check length difference
            if abs(len(lemma1) - len(lemma2)) <= 3:
                return True
        
        return False
    
    def _get_common_prefix(self, str1: str, str2: str) -> str:
        """Return common prefix of two strings"""
        min_length = min(len(str1), len(str2))
        common_prefix = []
        
        for i in range(min_length):
            if str1[i] == str2[i]:
                common_prefix.append(str1[i])
            else:
                break
        
        return ''.join(common_prefix)

# ============================================================================
# 📊 EXCEL EXPORTER (UPDATED WITH ROR INTEGRATION AND FIXED NORMALIZATION)
# ============================================================================

class ExcelExporter:
    def __init__(self, data_processor: DataProcessor, ror_client: RORClient,
                 failed_tracker: FailedDOITracker):
        self.processor = data_processor
        self.ror_client = ror_client
        self.failed_tracker = failed_tracker

        self.references_counter = Counter()
        self.citations_counter = Counter()
        self.ref_references_counter = Counter()
        self.ref_citations_counter = Counter()
        self.cite_references_counter = Counter()
        self.cite_citations_counter = Counter()

        self.analyzed_results = {}
        self.ref_results = {}
        self.citing_results = {}

        self.doi_to_source_counts = defaultdict(lambda: defaultdict(int))
        self.source_dois = {
            'analyzed': set(),
            'ref': set(),
            'citing': set()
        }

        self.ref_to_analyzed = defaultdict(list)
        self.analyzed_to_citing = defaultdict(list)

        # CHANGE: Simplify author structure - use only normalized_name as key
        self.author_stats = defaultdict(lambda: {
            'normalized_name': '',
            'orcid': set(),  # ORCID set for one author
            'affiliation': '',
            'country': '',
            'total_count': 0,  # Sum of normalized values
            'normalized_analyzed': 0,  # Only normalized value for analyzed
            'article_count_analyzed': 0,  # Absolute article count in analyzed
            'normalized_reference': 0,
            'normalized_citing': 0
        })

        # CHANGE: Simplify affiliation structure
        self.affiliation_stats = defaultdict(lambda: {
            'colab_id': '',
            'website': '',
            'countries': [],
            'total_count': 0,  # Sum of normalized values
            'normalized_analyzed': 0,  # Only normalized value for analyzed
            'article_count_analyzed': 0,  # Absolute article count in analyzed
            'normalized_reference': 0,
            'normalized_citing': 0
        })

        self.affiliation_country_stats = defaultdict(lambda: defaultdict(int))
        self.current_year = datetime.now().year

        # Initialize keywords analyzer
        self.title_keywords_analyzer = TitleKeywordsAnalyzer()

        # Statistics for Terms and Topics
        self.terms_topics_stats = defaultdict(lambda: {
            'type': '',
            'analyzed_count': 0,
            'reference_count': 0,
            'citing_count': 0,
            'years': [],
            'first_year': None,
            'peak_year': None,
            'peak_count': 0
        })

        # Flag for enabling ROR analysis
        self.enable_ror_analysis = False

    def _validate_data_before_processing(self, results: Dict[str, Dict], source_type: str) -> Dict[str, Dict]:
        """Валидация данных перед обработкой в Excel"""
        validated_results = {}
        error_count = 0
        
        for doi, result in results.items():
            try:
                if result is None:
                    st.warning(f"⚠️ {source_type}: Result for {doi} is None")
                    validated_results[doi] = self._create_empty_article_data(doi, source_type)
                    error_count += 1
                    continue
                    
                if not isinstance(result, dict):
                    st.warning(f"⚠️ {source_type}: Result for {doi} is not dict, type: {type(result)}")
                    validated_results[doi] = self._create_empty_article_data(doi, source_type)
                    error_count += 1
                    continue
                    
                # Проверяем наличие обязательных ключей
                required_keys = ['publication_info', 'authors', 'countries', 'topics_info']
                for key in required_keys:
                    if key not in result:
                        result[key] = {} if key == 'publication_info' or key == 'topics_info' else []
                    elif result[key] is None:
                        result[key] = {} if key == 'publication_info' or key == 'topics_info' else []
                
                # Проверяем вложенные структуры
                if 'publication_info' in result and isinstance(result['publication_info'], dict):
                    pub_info_keys = ['title', 'journal', 'year', 'publication_date']
                    for key in pub_info_keys:
                        if key not in result['publication_info']:
                            result['publication_info'][key] = ''
                        elif result['publication_info'][key] is None:
                            result['publication_info'][key] = ''
                
                validated_results[doi] = result
                
            except Exception as e:
                st.warning(f"⚠️ {source_type}: Error validating {doi}: {str(e)}")
                validated_results[doi] = self._create_empty_article_data(doi, source_type)
                error_count += 1
        
        if error_count > 0:
            st.warning(f"⚠️ Found {error_count} invalid records in {source_type} data")
        
        return validated_results
    
    def _create_empty_article_data(self, doi: str, source_type: str) -> Dict:
        """Создание пустых данных для статьи"""
        return {
            'doi': doi,
            'status': 'failed',
            'error': 'Data validation failed',
            'publication_info': {
                'title': f'Invalid data ({source_type})',
                'journal': '',
                'year': '',
                'publication_date': '',
                'citation_count_crossref': 0,
                'citation_count_openalex': 0
            },
            'authors': [],
            'countries': [],
            'topics_info': {},
            'orcid_urls': [],
            'references': [],
            'citations': [],
            'references_count': 0,
            'pages_formatted': '',
            'quick_insights': {}
        }
    
    def _correct_country_for_author(self, author_key: str, affiliation_stats: Dict[str, Any]) -> str:
        """Correct country for author based on affiliation statistics"""
        author_info = self.author_stats[author_key]
        if not author_info['affiliation']:
            return author_info['country']
    
        affiliation = author_info['affiliation']
        
        # First try to determine country from affiliation itself
        country_from_affiliation = self._get_country_from_affiliation(affiliation)
        if country_from_affiliation:
            return country_from_affiliation
        
        # If not successful, use affiliation statistics
        if affiliation in affiliation_stats and affiliation_stats[affiliation]['countries']:
            countries = affiliation_stats[affiliation]['countries']
            if countries:
                country_counter = Counter(countries)
                most_common_country = country_counter.most_common(1)[0][0]
    
                if author_info['country'] != most_common_country:
                    website = affiliation_stats[affiliation].get('website', '')
                    if website:
                        domain_match = re.search(r'\.([a-z]{2,3})$', website.lower())
                        if domain_match:
                            domain_zone = domain_match.group(1).upper()
                            domain_to_country = {
                                'RU': 'RU', 'SU': 'RU',
                                'US': 'US', 'COM': 'US', 'ORG': 'US', 'NET': 'US',
                                'UK': 'GB', 'GB': 'GB', 'CO.UK': 'GB',
                                'DE': 'DE', 'FR': 'FR', 'IT': 'IT', 'ES': 'ES',
                                'CN': 'CN', 'JP': 'JP', 'KR': 'KR', 'IN': 'IN',
                                'AU': 'AU', 'CA': 'CA', 'BR': 'BR', 'MX': 'MX'
                            }
    
                            if domain_zone in domain_to_country:
                                website_country = domain_to_country[domain_zone]
                                if website_country == most_common_country:
                                    return most_common_country
    
                        if len(countries) >= 3:
                            country_freq = country_counter[most_common_country] / len(countries)
                            if country_freq >= 0.7:
                                return most_common_country
    
        return author_info['country']
        
    def _get_country_from_affiliation(self, affiliation: str) -> str:
        """Determine country from affiliation text"""
        if not affiliation:
            return ""
        
        affiliation_lower = affiliation.lower()
        
        # Use same country_codes dictionary from DataProcessor
        # Find it through self.processor.country_codes
        for country_name, country_code in self.processor.country_codes.items():
            country_lower = country_name.lower()
            # Look for whole word
            pattern = r'\b' + re.escape(country_lower) + r'\b'
            if re.search(pattern, affiliation_lower):
                return country_code
        
        # Look for country codes
        for country_name, country_code in self.processor.country_codes.items():
            if len(country_code) == 2:
                if re.search(r'\b' + country_code + r'\b', affiliation, re.IGNORECASE):
                    return country_code
        
        # Look for Russian
        russian_countries = {
            'россия': 'RU', 'рф': 'RU', 'российская': 'RU',
            'украина': 'UA', 'беларусь': 'BY', 'казахстан': 'KZ',
        }
        
        for ru_name, code in russian_countries.items():
            if ru_name in affiliation_lower:
                return code
        
        return ""
    
    def _calculate_annual_citation_rate(self, citation_count: int, publication_year_str: str) -> float:
        """Calculate average annual citations"""
        if not citation_count or not publication_year_str:
            return 0.0

        try:
            pub_year = int(publication_year_str)
            age = self.current_year - pub_year + 1
            if age <= 0:
                age = 1

            return citation_count / age
        except:
            return 0.0
          
    def _prepare_ror_data_with_progress(self, affiliations_list: List[str], progress_container=None) -> Dict[str, Dict]:
        """Prepare ROR data with progress bar"""
        if not self.enable_ror_analysis:
            st.info("ℹ️ ROR analysis disabled")
            return {}
            
        if not affiliations_list:
            st.warning("⚠️ Affiliation list is empty")
            return {}
            
        total_affiliations = len(affiliations_list)
        
        if progress_container:
            progress_text = progress_container.text(f"🔍 Searching ROR data for {total_affiliations} affiliations...")
            ror_progress_bar = progress_container.progress(0)
            status_text = progress_container.empty()
        else:
            progress_text = None
            ror_progress_bar = None
            status_text = None
        
        # Use parallel search via RORClient
        ror_data = self.ror_client.search_multiple_organizations(affiliations_list, progress_container)
        
        # IMPORTANT: Update affiliation statistics with obtained ROR data
        for affiliation, ror_info in ror_data.items():
            if affiliation in self.affiliation_stats:
                self.affiliation_stats[affiliation]['colab_id'] = ror_info.get('ror_id', '')
                self.affiliation_stats[affiliation]['website'] = ror_info.get('website', '')
        
        if progress_container and ror_progress_bar:
            ror_progress_bar.progress(1.0)
            if status_text:
                status_text.text(f"✅ ROR data collected for {len(ror_data)} affiliations")
        
        return ror_data

    def create_comprehensive_report(self, analyzed_results: Dict[str, Dict],
                                   ref_results: Dict[str, Dict] = None,
                                   citing_results: Dict[str, Dict] = None,
                                   filename: str = None,
                                   progress_container=None,
                                   enable_ror: bool = False) -> BytesIO:
    
        if filename is None:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = f"articles_analysis_comprehensive_{timestamp}.xlsx"
    
        if progress_container:
            progress_container.text(f"📊 Creating comprehensive report: {filename}")
    
        self.analyzed_results = analyzed_results
        self.ref_results = ref_results or {}
        self.citing_results = citing_results or {}
        
        # Set ROR analysis flag
        self.enable_ror_analysis = enable_ror
        
        if self.enable_ror_analysis and progress_container:
            progress_container.info("🔍 ROR analysis enabled. Organization data will be collected.")
    
        # Prepare summary data with ROR progress
        if progress_container:
            progress_container.text("📋 Preparing summary data...")
        self._prepare_summary_data()
    
        # Prepare ROR data with progress bar (if enabled)
        affiliations_list = list(self.affiliation_stats.keys())
        ror_data = {}
        if self.enable_ror_analysis and affiliations_list:
            if progress_container:
                progress_container.text(f"🔍 Collecting ROR data for {len(affiliations_list)} affiliations...")
            # Use same container for progress
            ror_data = self._prepare_ror_data_with_progress(affiliations_list, progress_container)
            
            if ror_data and progress_container:
                progress_container.success(f"✅ ROR data obtained for {len(ror_data)} out of {len(affiliations_list)} affiliations")
            elif progress_container:
                progress_container.warning(f"⚠️ Failed to obtain ROR data for affiliations")

        # Analyze keywords in titles
        if progress_container:
            progress_container.text("🔤 Analyzing keywords in titles...")
        
        # Extract titles from all sources
        analyzed_titles = []
        for result in analyzed_results.values():
            if result.get('status') == 'success':
                title = result.get('publication_info', {}).get('title', '')
                if title:
                    analyzed_titles.append(title)
        
        reference_titles = []
        for result in self.ref_results.values():
            if result.get('status') == 'success':
                title = result.get('publication_info', {}).get('title', '')
                if title:
                    reference_titles.append(title)
        
        citing_titles = []
        for result in self.citing_results.values():
            if result.get('status') == 'success':
                title = result.get('publication_info', {}).get('title', '')
                if title:
                    citing_titles.append(title)
        
        # Analyze keywords
        title_keywords_analysis = self.title_keywords_analyzer.analyze_titles(
            analyzed_titles, reference_titles, citing_titles
        )
        
        # Prepare data for Title keywords sheet
        title_keywords_data = self._prepare_title_keywords_data(title_keywords_analysis)
        
        # Prepare data for Terms and Topics sheet
        if progress_container:
            progress_container.text("🏷️ Preparing Terms and Topics data...")
        terms_topics_data = self._prepare_terms_topics_data()

        # Create Excel file in memory
        output = BytesIO()
        
        with pd.ExcelWriter(output, engine='openpyxl') as writer:
            if progress_container:
                progress_container.text("📑 Generating sheets...")

            # Create Excel tabs
            self._generate_excel_sheets(writer, analyzed_results, ref_results, citing_results, 
                                      title_keywords_data, terms_topics_data, progress_container)

        output.seek(0)
        return output

    def _generate_excel_sheets(self, writer, analyzed_results, ref_results, citing_results,
                             title_keywords_data, terms_topics_data, progress_container):
        """Generate all Excel sheets"""
        sheets = [
            ('Article_Analyzed', lambda: self._prepare_analyzed_articles(analyzed_results)),
            ('Author freq_analyzed', lambda: self._prepare_author_frequency(analyzed_results, "analyzed")),
            ('Journal freq_analyzed', lambda: self._prepare_journal_frequency(analyzed_results, "analyzed")),
            ('Affiliation freq_analyzed', lambda: self._prepare_affiliation_frequency(analyzed_results, "analyzed")),
            ('Country freq_analyzed', lambda: self._prepare_country_frequency(analyzed_results, "analyzed")),
            ('Article_ref', lambda: self._prepare_article_ref()),
            ('Author freq_ref', lambda: self._prepare_author_frequency(ref_results, "ref") if ref_results else []),
            ('Journal freq_ref', lambda: self._prepare_journal_frequency(ref_results, "ref") if ref_results else []),
            ('Affiliation freq_ref', lambda: self._prepare_affiliation_frequency(ref_results, "ref") if ref_results else []),
            ('Country freq_ref', lambda: self._prepare_country_frequency(ref_results, "ref") if ref_results else []),
            ('Article_citing', lambda: self._prepare_article_citing()),
            ('Author freq_citing', lambda: self._prepare_author_frequency(citing_results, "citing") if citing_results else []),
            ('Journal freq_citing', lambda: self._prepare_journal_frequency(citing_results, "citing") if citing_results else []),
            ('Affiliation freq_citing', lambda: self._prepare_affiliation_frequency(citing_results, "citing") if citing_results else []),
            ('Country freq_citing', lambda: self._prepare_country_frequency(citing_results, "citing") if citing_results else []),
            ('Author_summary', lambda: self._prepare_author_summary()),
            ('Affiliation_summary', lambda: self._prepare_affiliation_summary()),
            ('Time (Ref,analyzed)_connections', lambda: self._prepare_time_ref_analyzed_connections()),
            ('Time (analyzed,citing)_connections', lambda: self._prepare_time_analyzed_citing_connections()),
            ('Failed_DOI', lambda: self.failed_tracker.get_failed_for_excel()),
            ('Analysis_Stats', lambda: self._prepare_analysis_stats(analyzed_results, ref_results, citing_results)),
            ('Title keywords', lambda: title_keywords_data),
            ('Terms and Topics', lambda: terms_topics_data),
        ]

        for idx, (sheet_name, data_func) in enumerate(sheets):
            if progress_container:
                progress_container.text(f"  {idx+1}. {sheet_name}...")
            
            data = data_func()
            if data:
                df = pd.DataFrame(data)
                df.to_excel(writer, sheet_name=sheet_name, index=False)

    def _prepare_summary_data(self):
        total_analyzed_articles = len([r for r in self.analyzed_results.values() if r.get('status') == 'success'])
        total_ref_articles = len([r for r in self.ref_results.values() if r.get('status') == 'success'])
        total_citing_articles = len([r for r in self.citing_results.values() if r.get('status') == 'success'])

        # CHANGE: Temporary counters for correct normalization
        author_analyzed_counts = Counter()  # Author article count in analyzed
        affiliation_analyzed_counts = Counter()  # Affiliation article count in analyzed

        for doi, result in self.analyzed_results.items():
            if result.get('status') != 'success':
                continue

            self.source_dois['analyzed'].add(doi)

            # Update Terms and Topics statistics for analyzed articles
            self._update_terms_topics_stats(doi, result, 'analyzed')

            for ref_doi in result.get('references', []):
                self.ref_to_analyzed[ref_doi].append(doi)
                self.doi_to_source_counts[ref_doi]['ref'] += 1
                self.source_dois['ref'].add(ref_doi)

            for cite_doi in result.get('citations', []):
                self.analyzed_to_citing[doi].append(cite_doi)
                self.doi_to_source_counts[cite_doi]['citing'] += 1
                self.source_dois['citing'].add(cite_doi)

            # CHANGE: Count authors in analyzed articles
            for author in result.get('authors', []):
                full_name = author.get('name', '')
                if not full_name:
                    continue
            
                normalized_name = self.processor.normalize_author_name(full_name)
                # USE ONLY normalized_name as key
                key = normalized_name
                
                # Increase article counter for this author in analyzed
                author_analyzed_counts[key] += 1
            
                # Initialize author record if not exists
                if key not in self.author_stats:
                    self.author_stats[key] = {
                        'normalized_name': normalized_name,
                        'orcid': set(),
                        'affiliation': '',
                        'country': '',
                        'total_count': 0,
                        'normalized_analyzed': 0,
                        'article_count_analyzed': 0,
                        'normalized_reference': 0,
                        'normalized_citing': 0
                    }
            
                # Update ORCID as set
                if author.get('orcid'):
                    self.author_stats[key]['orcid'].add(self.processor._format_orcid_id(author.get('orcid', '')))
            
                # Determine affiliation
                if not self.author_stats[key]['affiliation'] and author.get('affiliation'):
                    self.author_stats[key]['affiliation'] = author.get('affiliation')[0] if author.get('affiliation') else ''
                
                # IMPORTANT FIX: Determine author country from his data
                if not self.author_stats[key]['country']:
                    # 1. Try to take from author_country (new field)
                    if 'author_country' in author and author['author_country']:
                        self.author_stats[key]['country'] = author['author_country']
                    # 2. If not, determine from affiliation
                    elif self.author_stats[key]['affiliation']:
                        country_from_aff = self._get_country_from_affiliation(self.author_stats[key]['affiliation'])
                        if country_from_aff:
                            self.author_stats[key]['country'] = country_from_aff
                    # 3. Fallback: from article
                    elif result.get('countries'):
                        self.author_stats[key]['country'] = result.get('countries')[0] if result.get('countries') else ''
            
                self.author_stats[key]['normalized_name'] = normalized_name

            # CHANGE: Update affiliation statistics FOR ANALYZED
            unique_affiliations_in_article = set()
            for author in result.get('authors', []):
                for affiliation in author.get('affiliation', []):
                    if affiliation:
                        unique_affiliations_in_article.add(affiliation)

            # Count absolute article number for each affiliation in analyzed
            for affiliation in unique_affiliations_in_article:
                affiliation_analyzed_counts[affiliation] += 1
                
                # Initialize affiliation record if not exists
                if affiliation not in self.affiliation_stats:
                    self.affiliation_stats[affiliation] = {
                        'colab_id': '',
                        'website': '',
                        'countries': [],
                        'total_count': 0,
                        'normalized_analyzed': 0,
                        'article_count_analyzed': 0,
                        'normalized_reference': 0,
                        'normalized_citing': 0
                    }
                
                if result.get('countries'):
                    for country in result.get('countries'):
                        if country:
                            self.affiliation_stats[affiliation]['countries'].append(country)

        # CHANGE: After counting all analyzed articles, calculate normalized values FOR AUTHORS
        for author_key, count in author_analyzed_counts.items():
            if total_analyzed_articles > 0:
                normalized_value = count / total_analyzed_articles
                self.author_stats[author_key]['normalized_analyzed'] = normalized_value
                self.author_stats[author_key]['article_count_analyzed'] = count
                # Update total_count for author
                self.author_stats[author_key]['total_count'] += normalized_value

        # CHANGE: After counting all analyzed articles, calculate normalized values FOR AFFILIATIONS
        for affiliation, count in affiliation_analyzed_counts.items():
            if total_analyzed_articles > 0:
                normalized_value = count / total_analyzed_articles
                self.affiliation_stats[affiliation]['normalized_analyzed'] = normalized_value
                self.affiliation_stats[affiliation]['article_count_analyzed'] = count
                # Update total_count for affiliation
                self.affiliation_stats[affiliation]['total_count'] += normalized_value

        # Process ref results
        for doi, result in self.ref_results.items():
            if result.get('status') != 'success':
                continue

            # Update Terms and Topics statistics for reference articles
            self._update_terms_topics_stats(doi, result, 'reference')

            # CHANGE: Update author stats for ref articles - ONLY normalized values
            for author in result.get('authors', []):
                full_name = author.get('name', '')
                if not full_name:
                    continue

                normalized_name = self.processor.normalize_author_name(full_name)
                # USE ONLY normalized_name as key
                key = normalized_name

                # Calculate normalized value for ref articles
                if total_ref_articles > 0:
                    normalized_value = 1 / total_ref_articles
                    self.author_stats[key]['normalized_reference'] += normalized_value
                    self.author_stats[key]['total_count'] += normalized_value

                # Update ORCID as set
                if author.get('orcid'):
                    self.author_stats[key]['orcid'].add(self.processor._format_orcid_id(author.get('orcid', '')))

                if not self.author_stats[key]['affiliation'] and author.get('affiliation'):
                    self.author_stats[key]['affiliation'] = author.get('affiliation')[0] if author.get('affiliation') else ''

                if not self.author_stats[key]['country'] and result.get('countries'):
                    self.author_stats[key]['country'] = result.get('countries')[0] if result.get('countries') else ''

                self.author_stats[key]['normalized_name'] = normalized_name

            # CHANGE: Update affiliation stats for ref articles - ONLY normalized values
            unique_affiliations_in_article = set()
            for author in result.get('authors', []):
                for affiliation in author.get('affiliation', []):
                    if affiliation:
                        unique_affiliations_in_article.add(affiliation)

            if total_ref_articles > 0:
                normalized_aff_value = 1 / total_ref_articles
                for affiliation in unique_affiliations_in_article:
                    self.affiliation_stats[affiliation]['normalized_reference'] += normalized_aff_value
                    self.affiliation_stats[affiliation]['total_count'] += normalized_aff_value

        # Process citing results
        for doi, result in self.citing_results.items():
            if result.get('status') != 'success':
                continue

            # Update Terms and Topics statistics for citing articles
            self._update_terms_topics_stats(doi, result, 'citing')

            # CHANGE: Update author stats for citing articles - ONLY normalized values
            for author in result.get('authors', []):
                full_name = author.get('name', '')
                if not full_name:
                    continue

                normalized_name = self.processor.normalize_author_name(full_name)
                # USE ONLY normalized_name as key
                key = normalized_name

                # Calculate normalized value for citing articles
                if total_citing_articles > 0:
                    normalized_value = 1 / total_citing_articles
                    self.author_stats[key]['normalized_citing'] += normalized_value
                    self.author_stats[key]['total_count'] += normalized_value

                # Update ORCID as set
                if author.get('orcid'):
                    self.author_stats[key]['orcid'].add(self.processor._format_orcid_id(author.get('orcid', '')))

                if not self.author_stats[key]['affiliation'] and author.get('affiliation'):
                    self.author_stats[key]['affiliation'] = author.get('affiliation')[0] if author.get('affiliation') else ''

                if not self.author_stats[key]['country'] and result.get('countries'):
                    self.author_stats[key]['country'] = result.get('countries')[0] if result.get('countries') else ''

                self.author_stats[key]['normalized_name'] = normalized_name

            # CHANGE: Update affiliation stats for citing articles - ONLY normalized values
            unique_affiliations_in_article = set()
            for author in result.get('authors', []):
                for affiliation in author.get('affiliation', []):
                    if affiliation:
                        unique_affiliations_in_article.add(affiliation)

            if total_citing_articles > 0:
                normalized_aff_value = 1 / total_citing_articles
                for affiliation in unique_affiliations_in_article:
                    self.affiliation_stats[affiliation]['normalized_citing'] += normalized_aff_value
                    self.affiliation_stats[affiliation]['total_count'] += normalized_aff_value

    def _update_terms_topics_stats(self, doi: str, result: Dict, source_type: str):
        """Update terms and topics statistics"""
        if result.get('status') != 'success':
            return

        topics_info = result.get('topics_info', {})
        pub_info = result.get('publication_info', {})
        year_str = pub_info.get('year', '')

        try:
            year = int(year_str) if year_str and year_str.isdigit() else None
        except:
            year = None

        # Update statistics for each term type
        term_types = ['topic', 'subfield', 'field', 'domain']
        for term_type in term_types:
            term = topics_info.get(term_type, '')
            if term:
                key = f"{term_type}:{term}"
                
                if source_type == 'analyzed':
                    self.terms_topics_stats[key]['analyzed_count'] += 1
                elif source_type == 'reference':
                    self.terms_topics_stats[key]['reference_count'] += 1
                elif source_type == 'citing':
                    self.terms_topics_stats[key]['citing_count'] += 1
                
                self.terms_topics_stats[key]['type'] = term_type.capitalize()
                
                if year:
                    self.terms_topics_stats[key]['years'].append(year)
                    
                    # Update first year
                    if self.terms_topics_stats[key]['first_year'] is None or year < self.terms_topics_stats[key]['first_year']:
                        self.terms_topics_stats[key]['first_year'] = year
                    
                    # Update peak year
                    year_count = self.terms_topics_stats[key]['years'].count(year)
                    if year_count > self.terms_topics_stats[key]['peak_count']:
                        self.terms_topics_stats[key]['peak_year'] = year
                        self.terms_topics_stats[key]['peak_count'] = year_count

        # Update statistics for concepts
        concepts = topics_info.get('concepts', [])
        for concept in concepts:
            key = f"concept:{concept}"
            
            if source_type == 'analyzed':
                self.terms_topics_stats[key]['analyzed_count'] += 1
            elif source_type == 'reference':
                self.terms_topics_stats[key]['reference_count'] += 1
            elif source_type == 'citing':
                self.terms_topics_stats[key]['citing_count'] += 1
            
            self.terms_topics_stats[key]['type'] = 'Concept'
            
            if year:
                self.terms_topics_stats[key]['years'].append(year)
                
                # Update first year
                if self.terms_topics_stats[key]['first_year'] is None or year < self.terms_topics_stats[key]['first_year']:
                    self.terms_topics_stats[key]['first_year'] = year
                
                # Update peak year
                year_count = self.terms_topics_stats[key]['years'].count(year)
                if year_count > self.terms_topics_stats[key]['peak_count']:
                    self.terms_topics_stats[key]['peak_year'] = year
                    self.terms_topics_stats[key]['peak_count'] = year_count
        
    def _prepare_title_keywords_data(self, keywords_analysis: dict) -> List[Dict]:
            """Prepare data for Title keywords sheet with grouping by lemmas"""
            data = []
            
            # Total articles for normalization
            total_analyzed = keywords_analysis['analyzed']['total_titles']
            total_reference = keywords_analysis['reference']['total_titles']
            total_citing = keywords_analysis['citing']['total_titles']
            
            # Collect all unique lemmas
            all_lemmas = {}
            
            # Process analyzed articles
            for word_info in keywords_analysis['analyzed']['words']:
                lemma = word_info['lemma']
                if lemma not in all_lemmas:
                    all_lemmas[lemma] = {
                        'type': word_info['type'],
                        'analyzed': 0,
                        'reference': 0,
                        'citing': 0,
                        'analyzed_variants': Counter(),
                        'reference_variants': Counter(),
                        'citing_variants': Counter()
                    }
                all_lemmas[lemma]['analyzed'] = word_info['count']
                all_lemmas[lemma]['analyzed_variants'] = word_info['variants']
            
            # Process reference articles
            for word_info in keywords_analysis['reference']['words']:
                lemma = word_info['lemma']
                if lemma not in all_lemmas:
                    all_lemmas[lemma] = {
                        'type': word_info['type'],
                        'analyzed': 0,
                        'reference': 0,
                        'citing': 0,
                        'analyzed_variants': Counter(),
                        'reference_variants': Counter(),
                        'citing_variants': Counter()
                    }
                all_lemmas[lemma]['reference'] = word_info['count']
                all_lemmas[lemma]['reference_variants'] = word_info['variants']
            
            # Process citing articles
            for word_info in keywords_analysis['citing']['words']:
                lemma = word_info['lemma']
                if lemma not in all_lemmas:
                    all_lemmas[lemma] = {
                        'type': word_info['type'],
                        'analyzed': 0,
                        'reference': 0,
                        'citing': 0,
                        'analyzed_variants': Counter(),
                        'reference_variants': Counter(),
                        'citing_variants': Counter()
                    }
                all_lemmas[lemma]['citing'] = word_info['count']
                all_lemmas[lemma]['citing_variants'] = word_info['variants']
            
            # Merge similar lemmas between types (analyzed, reference, citing)
            merged_lemmas = {}
            lemmas_to_merge = {}
            
            # Find similar lemmas
            all_lemma_list = list(all_lemmas.keys())
            for i in range(len(all_lemma_list)):
                lemma1 = all_lemma_list[i]
                if lemma1 in lemmas_to_merge:
                    continue
                    
                for j in range(i+1, len(all_lemma_list)):
                    lemma2 = all_lemma_list[j]
                    if lemma2 in lemmas_to_merge:
                        continue
                    
                    # Check if lemmas are similar using improved analyzer
                    if self.title_keywords_analyzer._are_similar_lemmas(lemma1, lemma2):
                        # Choose shorter lemma as main
                        if len(lemma1) <= len(lemma2):
                            main_lemma = lemma1
                            secondary_lemma = lemma2
                        else:
                            main_lemma = lemma2
                            secondary_lemma = lemma1
                        
                        if main_lemma not in lemmas_to_merge:
                            lemmas_to_merge[main_lemma] = []
                        
                        lemmas_to_merge[main_lemma].append(secondary_lemma)
                        lemmas_to_merge[secondary_lemma] = [main_lemma]
            
            # Merge data
            for lemma, stats in all_lemmas.items():
                if lemma in lemmas_to_merge and lemma not in lemmas_to_merge.get(lemma, []):
                    # This lemma will be merged with another
                    continue
                
                # Check if need to merge this lemma with others
                if lemma in lemmas_to_merge:
                    main_lemma = lemma
                    # Create new record for main lemma
                    merged_stats = {
                        'type': stats['type'],
                        'analyzed': stats['analyzed'],
                        'reference': stats['reference'],
                        'citing': stats['citing'],
                        'analyzed_variants': stats['analyzed_variants'].copy(),
                        'reference_variants': stats['reference_variants'].copy(),
                        'citing_variants': stats['citing_variants'].copy()
                    }
                    
                    # Merge with secondary lemmas
                    for secondary_lemma in lemmas_to_merge[lemma]:
                        if secondary_lemma in all_lemmas:
                            sec_stats = all_lemmas[secondary_lemma]
                            merged_stats['analyzed'] += sec_stats['analyzed']
                            merged_stats['reference'] += sec_stats['reference']
                            merged_stats['citing'] += sec_stats['citing']
                            
                            # Merge variants
                            for variant, count in sec_stats['analyzed_variants'].items():
                                merged_stats['analyzed_variants'][variant] += count
                            for variant, count in sec_stats['reference_variants'].items():
                                merged_stats['reference_variants'][variant] += count
                            for variant, count in sec_stats['citing_variants'].items():
                                merged_stats['citing_variants'][variant] += count
                    
                    merged_lemmas[main_lemma] = merged_stats
                else:
                    # Lemma doesn't require merging
                    merged_lemmas[lemma] = stats
            
            # Create data rows
            for lemma, stats in merged_lemmas.items():
                # Calculate normalized values
                analyzed_norm = stats['analyzed'] / total_analyzed if total_analyzed > 0 else 0
                reference_norm = stats['reference'] / total_reference if total_reference > 0 else 0
                citing_norm = stats['citing'] / total_citing if total_citing > 0 else 0
                total_norm = analyzed_norm + reference_norm + citing_norm
                
                # Collect all word variants
                all_variants = set()
                variants_info = []
                
                # Variants from analyzed articles
                if stats['analyzed_variants']:
                    for variant, count in stats['analyzed_variants'].most_common(3):
                        all_variants.add(variant)
                        variants_info.append(f"{variant}({count})")
                
                # Variants from reference articles
                if stats['reference_variants']:
                    for variant, count in stats['reference_variants'].most_common(3):
                        all_variants.add(variant)
                        if variant not in [v.split('(')[0] for v in variants_info]:
                            variants_info.append(f"{variant}({count})")
                
                # Variants from citing articles
                if stats['citing_variants']:
                    for variant, count in stats['citing_variants'].most_common(3):
                        all_variants.add(variant)
                        if variant not in [v.split('(')[0] for v in variants_info]:
                            variants_info.append(f"{variant}({count})")
                
                # Format variants string
                variants_str = ', '.join(sorted(all_variants))
                
                data.append({
                    'Title term': lemma,
                    'Variants': variants_str,
                    'Type': stats['type'],
                    'Analyzed count': stats['analyzed'],
                    'Reference count': stats['reference'],
                    'Citing Count': stats['citing'],
                    'Analyzed norm count': round(analyzed_norm, 4),
                    'Reference norm count': round(reference_norm, 4),
                    'Citing norm Count': round(citing_norm, 4),
                    'Total norm count': round(total_norm, 4)
                })
            
            # Sort by Total norm count (descending)
            data.sort(key=lambda x: x['Total norm count'], reverse=True)
            
            return data

    def _prepare_terms_topics_data(self) -> List[Dict]:
        """Prepare data for Terms and Topics sheet"""
        data = []
        
        # Total articles for normalization
        total_analyzed = len([r for r in self.analyzed_results.values() if r.get('status') == 'success'])
        total_reference = len([r for r in self.ref_results.values() if r.get('status') == 'success'])
        total_citing = len([r for r in self.citing_results.values() if r.get('status') == 'success'])
        
        for key, stats in self.terms_topics_stats.items():
            if stats['analyzed_count'] == 0 and stats['reference_count'] == 0 and stats['citing_count'] == 0:
                continue
            
            # Extract term from key
            if ':' in key:
                term = key.split(':', 1)[1]
            else:
                term = key
            
            # Calculate normalized values
            analyzed_norm = stats['analyzed_count'] / total_analyzed if total_analyzed > 0 else 0
            reference_norm = stats['reference_count'] / total_reference if total_reference > 0 else 0
            citing_norm = stats['citing_count'] / total_citing if total_citing > 0 else 0
            total_norm = analyzed_norm + reference_norm + citing_norm
            
            # Calculate count for last 5 years
            recent_5_years_count = 0
            if stats['years']:
                current_year = datetime.now().year
                for year in stats['years']:
                    if year and year >= current_year - 5:
                        recent_5_years_count += 1
            
            data.append({
                'Term': term,
                'Type': stats['type'],
                'Analyzed count': stats['analyzed_count'],
                'Reference count': stats['reference_count'],
                'Citing Count': stats['citing_count'],
                'Analyzed norm count': round(analyzed_norm, 4),
                'Reference norm count': round(reference_norm, 4),
                'Citing norm Count': round(citing_norm, 4),
                'Total norm count': round(total_norm, 4),
                'First_Year': stats['first_year'] if stats['first_year'] else '',
                'Peak_Year': stats['peak_year'] if stats['peak_year'] else '',
                'Recent_5_Years_Count': recent_5_years_count
            })
        
        # Sort by Total norm count (descending)
        data.sort(key=lambda x: x['Total norm count'], reverse=True)
        
        return data

    def _prepare_analyzed_articles(self, results: Dict[str, Dict]) -> List[Dict]:
        return self._prepare_article_sheet(results, "analyzed")

    def _prepare_article_ref(self) -> List[Dict]:
        data = []

        processed_refs = {}
        for ref_doi, ref_result in self.ref_results.items():
            if ref_result.get('status') == 'success':
                processed_refs[ref_doi] = ref_result

        for ref_doi, ref_result in processed_refs.items():
            count = len(self.ref_to_analyzed.get(ref_doi, []))

            pub_info = ref_result.get('publication_info', {})
            authors = ref_result.get('authors', [])
            topics_info = ref_result.get('topics_info', {})

            orcid_urls = ref_result.get('orcid_urls', [])
            affiliations = list(set([aff for author in authors for aff in author.get('affiliation', []) if aff]))
            countries = ref_result.get('countries', [])

            annual_cr = self._calculate_annual_citation_rate(
                pub_info.get('citation_count_crossref', 0),
                pub_info.get('year', '')
            )
            annual_oa = self._calculate_annual_citation_rate(
                pub_info.get('citation_count_openalex', 0),
                pub_info.get('year', '')
            )

            row = {
                'doi': ref_doi,
                'publication_date': pub_info.get('publication_date', ''),
                'Title': pub_info.get('title', '')[:200] + ('...' if len(pub_info.get('title', '')) > 200 else ''),
                'authors': '; '.join([a['name'] for a in authors]),
                'ORCID ID 1; ORCID ID 2... ORCID ID last': '; '.join(orcid_urls),
                'author count': len(authors),
                'affiliations {aff 1; aff 2... aff last}': '; '.join(affiliations),
                'countries {country 1; ... country last}': '; '.join(countries),
                'Full journal Name': pub_info.get('journal', ''),
                'year': pub_info.get('year', ''),
                'Volume': pub_info.get('volume', ''),
                'Pages (or article number)': ref_result.get('pages_formatted', ''),
                'Citation counts (CR)': pub_info.get('citation_count_crossref', 0),
                'Citation counts (OA)': pub_info.get('citation_count_openalex', 0),
                'Annual cit counts (CR)': round(annual_cr, 2),
                'Annual cit counts (OA)': round(annual_oa, 2),
                'references_count': ref_result.get('references_count', 0),
                'count': count,
                'Topic': topics_info.get('topic', ''),
                'Subfield': topics_info.get('subfield', ''),
                'Field': topics_info.get('field', ''),
                'Domain': topics_info.get('domain', ''),
                'Concepts': '; '.join(topics_info.get('concepts', []))
            }

            data.append(row)

        for ref_doi in self.ref_to_analyzed:
            if ref_doi not in processed_refs:
                count = len(self.ref_to_analyzed.get(ref_doi, []))
                row = {
                    'doi': ref_doi,
                    'publication_date': '',
                    'Title': '',
                    'authors': '',
                    'ORCID ID 1; ORCID ID 2... ORCID ID last': '',
                    'author count': 0,
                    'affiliations {aff 1; aff 2... aff last}': '',
                    'countries {country 1; ... country last}': '',
                    'Full journal Name': '',
                    'year': '',
                    'Volume': '',
                    'Pages (or article number)': '',
                    'Citation counts (CR)': 0,
                    'Citation counts (OA)': 0,
                    'Annual cit counts (CR)': 0.0,
                    'Annual cit counts (OA)': 0.0,
                    'references_count': 0,
                    'count': count,
                    'Topic': '',
                    'Subfield': '',
                    'Field': '',
                    'Domain': '',
                    'Concepts': ''
                }
                data.append(row)

        data = self._sort_article_data_by_count_and_date(data)

        return data

    def _prepare_article_citing(self) -> List[Dict]:
        data = []

        processed_cites = {}
        for cite_doi, cite_result in self.citing_results.items():
            if cite_result.get('status') == 'success':
                processed_cites[cite_doi] = cite_result

        for cite_doi, cite_result in processed_cites.items():
            count = sum(1 for analyzed_list in self.analyzed_to_citing.values() if cite_doi in analyzed_list)

            pub_info = cite_result.get('publication_info', {})
            authors = cite_result.get('authors', [])
            topics_info = cite_result.get('topics_info', {})

            orcid_urls = cite_result.get('orcid_urls', [])
            affiliations = list(set([aff for author in authors for aff in author.get('affiliation', []) if aff]))
            countries = cite_result.get('countries', [])

            annual_cr = self._calculate_annual_citation_rate(
                pub_info.get('citation_count_crossref', 0),
                pub_info.get('year', '')
            )
            annual_oa = self._calculate_annual_citation_rate(
                pub_info.get('citation_count_openalex', 0),
                pub_info.get('year', '')
            )

            row = {
                'doi': cite_doi,
                'publication_date': pub_info.get('publication_date', ''),
                'Title': pub_info.get('title', '')[:200] + ('...' if len(pub_info.get('title', '')) > 200 else ''),
                'authors': '; '.join([a['name'] for a in authors]),
                'ORCID ID 1; ORCID ID 2... ORCID ID last': '; '.join(orcid_urls),
                'author count': len(authors),
                'affiliations {aff 1; aff 2... aff last}': '; '.join(affiliations),
                'countries {country 1; ... country last}': '; '.join(countries),
                'Full journal Name': pub_info.get('journal', ''),
                'year': pub_info.get('year', ''),
                'Volume': pub_info.get('volume', ''),
                'Pages (or article number)': cite_result.get('pages_formatted', ''),
                'Citation counts (CR)': pub_info.get('citation_count_crossref', 0),
                'Citation counts (OA)': pub_info.get('citation_count_openalex', 0),
                'Annual cit counts (CR)': round(annual_cr, 2),
                'Annual cit counts (OA)': round(annual_oa, 2),
                'references_count': cite_result.get('references_count', 0),
                'count': count,
                'Topic': topics_info.get('topic', ''),
                'Subfield': topics_info.get('subfield', ''),
                'Field': topics_info.get('field', ''),
                'Domain': topics_info.get('domain', ''),
                'Concepts': '; '.join(topics_info.get('concepts', []))
            }

            data.append(row)

        all_citing_dois = set()
        for analyzed_list in self.analyzed_to_citing.values():
            all_citing_dois.update(analyzed_list)

        for cite_doi in all_citing_dois:
            if cite_doi not in processed_cites:
                count = sum(1 for analyzed_list in self.analyzed_to_citing.values() if cite_doi in analyzed_list)
                row = {
                    'doi': cite_doi,
                    'publication_date': '',
                    'Title': '',
                    'authors': '',
                    'ORCID ID 1; ORCID ID 2... ORCID ID last': '',
                    'author count': 0,
                    'affiliations {aff 1; aff 2... aff last}': '',
                    'countries {country 1; ... country last}': '',
                    'Full journal Name': '',
                    'year': '',
                    'Volume': '',
                    'Pages (or article number)': '',
                    'Citation counts (CR)': 0,
                    'Citation counts (OA)': 0,
                    'Annual cit counts (CR)': 0.0,
                    'Annual cit counts (OA)': 0.0,
                    'references_count': 0,
                    'count': count,
                    'Topic': '',
                    'Subfield': '',
                    'Field': '',
                    'Domain': '',
                    'Concepts': ''
                }
                data.append(row)

        data = self._sort_article_data_by_count_and_date(data)

        return data

    def _sort_article_data_by_count_and_date(self, data: List[Dict]) -> List[Dict]:
        def sort_key(row):
            count = row.get('count', 0)
            date_str = row.get('publication_date', '')

            date_value = None
            if date_str:
                try:
                    for fmt in ['%Y-%m-%d', '%Y-%m', '%Y']:
                        try:
                            date_value = datetime.strptime(date_str[:len(fmt)], fmt)
                            break
                        except:
                            continue
                except:
                    date_value = None

            count_sort = -count

            if date_value:
                date_sort = -date_value.timestamp()
            else:
                date_sort = 0

            return (count_sort, date_sort)

        return sorted(data, key=sort_key)

    def _prepare_article_sheet(self, results: Dict[str, Dict], source_type: str) -> List[Dict]:
        data = []

        for doi, result in results.items():
            if result.get('status') != 'success':
                continue

            pub_info = result['publication_info']
            authors = result['authors']
            topics_info = result['topics_info']

            orcid_urls = result.get('orcid_urls', [])
            affiliations = list(set([aff for author in authors for aff in author.get('affiliation', []) if aff]))
            countries = result.get('countries', [])

            annual_cr = self._calculate_annual_citation_rate(
                pub_info.get('citation_count_crossref', 0),
                pub_info.get('year', '')
            )
            annual_oa = self._calculate_annual_citation_rate(
                pub_info.get('citation_count_openalex', 0),
                pub_info.get('year', '')
            )

            row = {
                'doi': doi,
                'publication_date': pub_info.get('publication_date', ''),
                'Title': pub_info.get('title', '')[:200] + ('...' if len(pub_info.get('title', '')) > 200 else ''),
                'authors': '; '.join([a['name'] for a in authors]),
                'ORCID ID 1; ORCID ID 2... ORCID ID last': '; '.join(orcid_urls),
                'author count': len(authors),
                'affiliations {aff 1; aff 2... aff last}': '; '.join(affiliations),
                'countries {country 1; ... country last}': '; '.join(countries),
                'Full journal Name': pub_info.get('journal', ''),
                'year': pub_info.get('year', ''),
                'Volume': pub_info.get('volume', ''),
                'Pages (or article number)': result.get('pages_formatted', ''),
                'Citation counts (CR)': pub_info.get('citation_count_crossref', 0),
                'Citation counts (OA)': pub_info.get('citation_count_openalex', 0),
                'Annual cit counts (CR)': round(annual_cr, 2),
                'Annual cit counts (OA)': round(annual_oa, 2),
                'references_count': result.get('references_count', 0),
                'Topic': topics_info.get('topic', ''),
                'Subfield': topics_info.get('subfield', ''),
                'Field': topics_info.get('field', ''),
                'Domain': topics_info.get('domain', ''),
                'Concepts': '; '.join(topics_info.get('concepts', []))
            }

            data.append(row)

        return data
    
    def _prepare_author_frequency(self, results: Dict[str, Dict], source_type: str) -> List[Dict]:
        author_counter = Counter()
        author_details = {}
    
        for doi, result in results.items():
            if result.get('status') != 'success':
                continue
    
            for author in result['authors']:
                full_name = author['name']
                normalized_name = self.processor.normalize_author_name(full_name)
    
                # USE ONLY normalized_name as key
                key = normalized_name
    
                author_counter[key] += 1
    
                if key not in author_details:
                    affiliation = author['affiliation'][0] if author.get('affiliation') else ""
                    orcid = author.get('orcid', '')
                    
                    # IMPORTANT FIX: Use author country, not article country
                    country = ""
                    
                    # 1. Try to take author country from data (new author_country field)
                    if 'author_country' in author and author['author_country']:
                        country = author['author_country']
                    
                    # 2. If not, determine from author affiliation (FIX)
                    elif affiliation:
                        # Use method from DataProcessor via self.processor
                        country = self._get_country_from_affiliation(affiliation)
                    
                    # 3. Fallback: if cannot determine, take from article
                    if not country and result.get('countries'):
                        country = result.get('countries', [''])[0]
    
                    author_details[key] = {
                        'orcid': self.processor._format_orcid_id(orcid) if orcid else '',
                        'affiliation': affiliation,
                        'country': country,
                        'normalized_name': normalized_name
                    }
    
        sorted_authors = sorted(author_counter.items(), key=lambda x: x[1], reverse=True)
    
        data = []
        for key, count in sorted_authors:
            details = author_details.get(key, {})
    
            if source_type == "analyzed":
                frequency_column = 'Frequency count {in the analyzed articles}'
            elif source_type == "ref":
                frequency_column = 'Frequency count {in the reference articles}'
            elif source_type == "citing":
                frequency_column = 'Frequency count {in the citing articles}'
            else:
                frequency_column = f'Frequency count {{{source_type}}}'
    
            row = {
                'Surname + Initial_normalized': details.get('normalized_name', ''),
                frequency_column: count,
                'ORCID ID': details.get('orcid', ''),
                'Affiliation': details.get('affiliation', ''),
                'Country': details.get('country', '')
            }
            data.append(row)
    
        return data
    
    def _prepare_author_summary(self) -> List[Dict]:
        data = []
        
        # CHANGE: Calculate total analyzed articles for normalization
        total_analyzed_articles = len([r for r in self.analyzed_results.values() if r.get('status') == 'success'])
    
        for key, stats in self.author_stats.items():
            if stats['total_count'] == 0:
                continue
    
            # CHANGE: Calculate normalized_analyzed based on article_count_analyzed
            normalized_analyzed = stats.get('normalized_analyzed', 0)
            
            # CHANGE: Total Count should be sum of normalized values, but normalized_analyzed already correct
            total_count = normalized_analyzed + stats['normalized_reference'] + stats['normalized_citing']
    
            # Convert ORCID set to string
            orcid_str = '; '.join(sorted(stats['orcid'])) if stats['orcid'] else ''
    
            # FIX: Use method from DataProcessor instead of non-existent one
            country = ""
            if stats['affiliation']:
                # Use method from DataProcessor for country determination
                country = self._get_country_from_affiliation(stats['affiliation'])
            
            # Fallback: use saved country or additional correction
            if not country:
                country = stats.get('country', '')
                if not country:
                    country = self._correct_country_for_author(key, self.affiliation_stats)
    
            row = {
                'Surname + Initial_normalized': stats['normalized_name'],
                'ORCID ID': orcid_str,
                'Affiliation': stats['affiliation'],
                'Country': country,
                'Total Count': round(total_count, 4),
                'Normalized Analyzed': round(normalized_analyzed, 4),
                'Normalized Reference': round(stats['normalized_reference'], 4),
                'Normalized Citing': round(stats['normalized_citing'], 4)
            }
            data.append(row)
    
        data.sort(key=lambda x: x['Total Count'], reverse=True)
    
        return data

    def _prepare_affiliation_summary(self) -> List[Dict]:
        data = []
        
        # CHANGE: Calculate total analyzed articles for normalization
        total_analyzed_articles = len([r for r in self.analyzed_results.values() if r.get('status') == 'success'])
    
        for affiliation, stats in self.affiliation_stats.items():
            if stats['total_count'] == 0:
                continue
    
            # Determine main country for affiliation
            main_country = ""
            if stats['countries']:
                country_counter = Counter(stats['countries'])
                most_common = country_counter.most_common(1)
                if most_common:
                    main_country = most_common[0][0]
    
            # CHANGE: Calculate normalized_analyzed based on article_count_analyzed
            normalized_analyzed = 0
            if total_analyzed_articles > 0:
                normalized_analyzed = stats['article_count_analyzed'] / total_analyzed_articles
            
            # CHANGE: Total Count should be sum of normalized values
            total_count = normalized_analyzed + stats['normalized_reference'] + stats['normalized_citing']

            # Check and format ROR data
            colab_id = stats.get('colab_id', '')
            website = stats.get('website', '')
            
            # If ROR analysis was enabled but data not found, add note
            if self.enable_ror_analysis and not colab_id:
                # Can add note that ROR not found
                colab_id = "ROR not found"
    
            row = {
                'Affiliation': affiliation,
                'Colab ID': colab_id,
                'Web Site': website,
                'Main Country': main_country,
                'total count': round(total_count, 4),
                'Normalized analyzed': round(normalized_analyzed, 4),
                'Normalized reference': round(stats['normalized_reference'], 4),
                'Normalized citing': round(stats['normalized_citing'], 4)
            }
            data.append(row)
    
        data.sort(key=lambda x: x['total count'], reverse=True)
        
        # Log result
        ror_found = sum(1 for row in data if row['Colab ID'] and row['Colab ID'] != "ROR not found")
        if self.enable_ror_analysis:
            st.info(f"📊 In Affiliation_summary: {ror_found} records with ROR ID out of {len(data)} affiliations")
    
        return data

    def _prepare_time_ref_analyzed_connections(self) -> List[Dict]:
        data = []

        for ref_doi, analyzed_dois in self.ref_to_analyzed.items():
            ref_result = self.ref_results.get(ref_doi, {})
            if ref_result.get('status') != 'success':
                continue

            ref_pub_info = ref_result.get('publication_info', {})
            ref_date_str = ref_pub_info.get('publication_date', '')

            ref_date = self._parse_date_string(ref_date_str)

            for analyzed_doi in analyzed_dois:
                analyzed_result = self.analyzed_results.get(analyzed_doi, {})
                if analyzed_result.get('status') != 'success':
                    continue

                analyzed_pub_info = analyzed_result.get('publication_info', {})
                analyzed_date_str = analyzed_pub_info.get('publication_date', '')

                analyzed_date = self._parse_date_string(analyzed_date_str)

                difference_days = self._calculate_date_difference(analyzed_date, ref_date)

                row = {
                    'Ref DOI': ref_doi,
                    'Analyzed DOI': analyzed_doi,
                    'publication date Ref': ref_date_str,
                    'publication date analyzed': analyzed_date_str,
                    'difference (days)': difference_days if difference_days is not None else ''
                }
                data.append(row)

        data_with_diff = [row for row in data if row['difference (days)'] not in ['', None]]
        data_without_diff = [row for row in data if row['difference (days)'] in ['', None]]

        data_with_diff.sort(key=lambda x: x['difference (days)'])

        return data_with_diff + data_without_diff

    def _prepare_time_analyzed_citing_connections(self) -> List[Dict]:
        data = []

        for analyzed_doi, citing_dois in self.analyzed_to_citing.items():
            analyzed_result = self.analyzed_results.get(analyzed_doi, {})
            if analyzed_result.get('status') != 'success':
                continue

            analyzed_pub_info = analyzed_result.get('publication_info', {})
            analyzed_date_str = analyzed_pub_info.get('publication_date', '')

            analyzed_date = self._parse_date_string(analyzed_date_str)

            for citing_doi in citing_dois:
                citing_result = self.citing_results.get(citing_doi, {})
                if citing_result.get('status') != 'success':
                    continue

                citing_pub_info = citing_result.get('publication_info', {})
                citing_date_str = citing_pub_info.get('publication_date', '')

                citing_date = self._parse_date_string(citing_date_str)

                difference_days = self._calculate_date_difference(citing_date, analyzed_date)

                row = {
                    'Analyzed DOI': analyzed_doi,
                    'Citing DOI': citing_doi,
                    'publication date analyzed': analyzed_date_str,
                    'publication date citing': citing_date_str,
                    'difference (days)': difference_days if difference_days is not None else ''
                }
                data.append(row)

        data_with_diff = [row for row in data if row['difference (days)'] not in ['', None]]
        data_without_diff = [row for row in data if row['difference (days)'] in ['', None]]

        data_with_diff.sort(key=lambda x: x['difference (days)'])

        return data_with_diff + data_without_diff

    def _parse_date_string(self, date_str: str) -> Optional[datetime]:
        if not date_str:
            return None

        date_str = date_str.strip()

        try:
            if re.match(r'^\d{4}-\d{1,2}-\d{1,2}$', date_str):
                parts = date_str.split('-')
                year = int(parts[0])
                month = int(parts[1])
                day = int(parts[2])
                return datetime(year, month, day)

            elif re.match(r'^\d{4}-\d{1,2}$', date_str):
                parts = date_str.split('-')
                year = int(parts[0])
                month = int(parts[1])
                return datetime(year, month, 15)

            elif re.match(r'^\d{4}$', date_str):
                year = int(date_str)
                return datetime(year, 7, 1)

            elif re.match(r'^\d{4}/\d{1,2}/\d{1,2}$', date_str):
                parts = date_str.split('/')
                year = int(parts[0])
                month = int(parts[1])
                day = int(parts[2])
                return datetime(year, month, day)

            elif re.match(r'^\d{4}/\d{1,2}$', date_str):
                parts = date_str.split('/')
                year = int(parts[0])
                month = int(parts[1])
                return datetime(year, month, 15)

            elif re.match(r'^\d{1,2}\.\d{1,2}\.\d{4}$', date_str):
                parts = date_str.split('.')
                day = int(parts[0])
                month = int(parts[1])
                year = int(parts[2])
                return datetime(year, month, day)

            elif re.match(r'^\d{1,2}/\d{1,2}/\d{4}$', date_str):
                parts = date_str.split('/')
                month = int(parts[0])
                day = int(parts[1])
                year = int(parts[2])
                return datetime(year, month, day)

            elif re.match(r'^\d{4}\.\d{1,2}\.\d{1,2}$', date_str):
                parts = date_str.split('.')
                year = int(parts[0])
                month = int(parts[1])
                day = int(parts[2])
                return datetime(year, month, day)

        except (ValueError, IndexError):
            pass

        year_match = re.search(r'\b(19\d{2}|20\d{2})\b', date_str)
        if year_match:
            try:
                year = int(year_match.group(1))
                return datetime(year, 7, 1)
            except:
                pass

        return None

    def _calculate_date_difference(self, date1: Optional[datetime], date2: Optional[datetime]) -> Optional[int]:
        if not date1 or not date2:
            return None

        try:
            difference = (date1 - date2).days

            if abs(difference) > 10000:
                if date1.year == date2.year:
                    return (date1 - datetime(date1.year, 1, 1)).days - (date2 - datetime(date2.year, 1, 1)).days

            return difference
        except:
            return None

    def _prepare_journal_frequency(self, results: Dict[str, Dict], source_type: str) -> List[Dict]:
        """Prepare data for Journal freq sheet with citation metrics"""
        journal_counter = Counter()
        journal_citation_cr = defaultdict(list)  # Crossref citations list for each journal
        journal_citation_oa = defaultdict(list)  # OpenAlex citations list for each journal
        journal_articles = defaultdict(list)  # Article list for each journal (for additional info)

        # Determine which source to take citation data from
        if source_type == "analyzed":
            source_data = self.analyzed_results
        elif source_type == "ref":
            source_data = self.ref_results
        elif source_type == "citing":
            source_data = self.citing_results
        else:
            source_data = results

        for doi, result in results.items():
            if result.get('status') != 'success':
                continue

            journal = result['publication_info'].get('journal', '')
            if journal:
                journal_counter[journal] += 1
                
                # Get citation data from corresponding source
                if doi in source_data and source_data[doi].get('status') == 'success':
                    source_result = source_data[doi]
                    pub_info = source_result.get('publication_info', {})
                    
                    # Add Crossref citations
                    cr_citations = pub_info.get('citation_count_crossref', 0)
                    if cr_citations > 0:
                        journal_citation_cr[journal].append(cr_citations)
                    
                    # Add OpenAlex citations
                    oa_citations = pub_info.get('citation_count_openalex', 0)
                    if oa_citations > 0:
                        journal_citation_oa[journal].append(oa_citations)
                    
                    # Save article for additional info
                    journal_articles[journal].append({
                        'doi': doi,
                        'title': pub_info.get('title', ''),
                        'year': pub_info.get('year', ''),
                        'cr_citations': cr_citations,
                        'oa_citations': oa_citations
                    })

        sorted_journals = sorted(journal_counter.items(), key=lambda x: x[1], reverse=True)

        data = []
        for journal, count in sorted_journals:
            # Calculate Crossref citation metrics
            cr_citations_list = journal_citation_cr.get(journal, [])
            total_cr = sum(cr_citations_list)
            avg_cr = total_cr / len(cr_citations_list) if cr_citations_list else 0
            
            # Calculate median for Crossref
            median_cr = 0
            if cr_citations_list:
                sorted_cr = sorted(cr_citations_list)
                n = len(sorted_cr)
                if n % 2 == 1:
                    median_cr = sorted_cr[n // 2]
                else:
                    median_cr = (sorted_cr[n // 2 - 1] + sorted_cr[n // 2]) / 2
            
            # Calculate OpenAlex citation metrics
            oa_citations_list = journal_citation_oa.get(journal, [])
            total_oa = sum(oa_citations_list)
            avg_oa = total_oa / len(oa_citations_list) if oa_citations_list else 0
            
            # Calculate median for OpenAlex
            median_oa = 0
            if oa_citations_list:
                sorted_oa = sorted(oa_citations_list)
                n = len(sorted_oa)
                if n % 2 == 1:
                    median_oa = sorted_oa[n // 2]
                else:
                    median_oa = (sorted_oa[n // 2 - 1] + sorted_oa[n // 2]) / 2
            
            row = {
                'Full Journal Name': journal,
                'Count': count,
                'Total citations (CR)': total_cr,
                'Total citations (OA)': total_oa,
                'Average citations (CR)': round(avg_cr, 2),
                'Average citations (OA)': round(avg_oa, 2),
                'Median citation (CR)': median_cr,
                'Median citation (OA)': median_oa,
                'Articles with CR data': len(cr_citations_list),
                'Articles with OA data': len(oa_citations_list)
            }
            data.append(row)

        return data

    def _prepare_affiliation_frequency(self, results: Dict[str, Dict], source_type: str) -> List[Dict]:
        affiliation_counter = Counter()

        for doi, result in results.items():
            if result.get('status') != 'success':
                continue

            unique_affiliations_in_article = set()
            for author in result.get('authors', []):
                for affiliation in author.get('affiliation', []):
                    if affiliation and affiliation.strip():
                        clean_aff = affiliation.strip()
                        unique_affiliations_in_article.add(clean_aff)

            for aff in unique_affiliations_in_article:
                affiliation_counter[aff] += 1

        unique_affiliations = list(set(affiliation_counter.keys()))

        affiliation_data = []

        for aff in unique_affiliations:
            row = {
                'Affiliation': aff,
                'Count': affiliation_counter[aff]
            }
            affiliation_data.append(row)

        affiliation_data.sort(key=lambda x: x['Count'], reverse=True)
        return affiliation_data

    def _prepare_country_frequency(self, results: Dict[str, Dict], source_type: str) -> List[Dict]:
        country_single_counter = Counter()
        country_combined_counter = Counter()

        for doi, result in results.items():
            if result.get('status') != 'success':
                continue

            countries = result.get('countries', [])
            if not countries:
                continue

            for country in countries:
                if country:
                    country_single_counter[country] += 1

            if len(countries) > 1:
                sorted_countries = sorted(countries)
                combination = ';'.join(sorted_countries)
                country_combined_counter[combination] += 1

        data = []

        for country, count in sorted(country_single_counter.items(), key=lambda x: x[1], reverse=True):
            data.append({
                'Country': country,
                'Type': 'single',
                'Count': count
            })

        for combination, count in sorted(country_combined_counter.items(), key=lambda x: x[1], reverse=True):
            data.append({
                'Country': combination,
                'Type': 'combined',
                'Count': count
            })

        return data

    def _prepare_analysis_stats(self, analyzed_results: Dict[str, Dict],
                               ref_results: Dict[str, Dict],
                               citing_results: Dict[str, Dict]) -> List[Dict]:
        stats = []

        analyzed_success = sum(1 for r in analyzed_results.values() if r.get('status') == 'success')
        analyzed_failed = len(analyzed_results) - analyzed_success

        stats.append({
            'Category': 'Analyzed Articles',
            'Total DOI': len(analyzed_results),
            'Successful': analyzed_success,
            'Failed': analyzed_failed,
            'Success Rate': f"{(analyzed_success/len(analyzed_results)*100):.1f}%" if analyzed_results else "0%"
        })

        if ref_results:
            ref_success = sum(1 for r in ref_results.values() if r.get('status') == 'success')
            ref_failed = len(ref_results) - ref_success

            stats.append({
                'Category': 'Reference Articles',
                'Total DOI': len(ref_results),
                'Successful': ref_success,
                'Failed': ref_failed,
                'Success Rate': f"{(ref_success/len(ref_results)*100):.1f}%" if ref_results else "0%"
            })

        if citing_results:
            cite_success = sum(1 for r in citing_results.values() if r.get('status') == 'success')
            cite_failed = len(citing_results) - cite_success

            stats.append({
                'Category': 'Citing Articles',
                'Total DOI': len(citing_results),
                'Successful': cite_success,
                'Failed': cite_failed,
                'Success Rate': f"{(cite_success/len(citing_results)*100):.1f}%" if citing_results else "0%"
            })

        total_dois = len(analyzed_results) + len(ref_results or {}) + len(citing_results or {})
        total_success = analyzed_success + (ref_success if ref_results else 0) + (cite_success if citing_results else 0)

        stats.append({
            'Category': 'TOTAL',
            'Total DOI': total_dois,
            'Successful': total_success,
            'Failed': total_dois - total_success,
            'Success Rate': f"{(total_success/total_dois*100):.1f}%" if total_dois > 0 else "0%"
        })

        return stats

    def update_counters(self, references: List[str], citations: List[str], source_type: str = "analyzed"):
        if source_type == "analyzed":
            counter_ref = self.references_counter
            counter_cite = self.citations_counter
        elif source_type == "ref":
            counter_ref = self.ref_references_counter
            counter_cite = self.ref_citations_counter
        elif source_type == "citing":
            counter_ref = self.cite_references_counter
            counter_cite = self.cite_citations_counter
        else:
            counter_ref = self.references_counter
            counter_cite = self.citations_counter

        for ref in references:
            if ref:
                counter_ref[ref] += 1

        for cite in citations:
            if cite:
                counter_cite[cite] += 1

# ============================================================================
# 🚀 MAIN SYSTEM CLASS (UPDATED FOR STREAMLIT WITH RESUME)
# ============================================================================

class ArticleAnalyzerSystem:
    def __init__(self):
        # Initialize system in session state
        if 'cache_manager' not in st.session_state:
            st.session_state.cache_manager = SmartCacheManager()
        if 'delay_manager' not in st.session_state:
            st.session_state.delay_manager = AdaptiveDelayManager()
        if 'failed_tracker' not in st.session_state:
            st.session_state.failed_tracker = FailedDOITracker()

        self.cache_manager = st.session_state.cache_manager
        self.delay_manager = st.session_state.delay_manager
        self.failed_tracker = st.session_state.failed_tracker

        self.crossref_client = CrossrefClient(self.cache_manager, self.delay_manager)
        self.openalex_client = OpenAlexClient(self.cache_manager, self.delay_manager)
        self.ror_client = RORClient(self.cache_manager)

        self.data_processor = DataProcessor(self.cache_manager)
        self.doi_processor = OptimizedDOIProcessor(
            self.cache_manager, self.delay_manager,
            self.data_processor, self.failed_tracker
        )
        self.excel_exporter = ExcelExporter(self.data_processor, self.ror_client, self.failed_tracker)

        # Initialize data in session state
        if 'analyzed_results' not in st.session_state:
            st.session_state.analyzed_results = {}
        if 'ref_results' not in st.session_state:
            st.session_state.ref_results = {}
        if 'citing_results' not in st.session_state:
            st.session_state.citing_results = {}
        if 'processing_complete' not in st.session_state:
            st.session_state.processing_complete = False
        if 'resume_available' not in st.session_state:
            st.session_state.resume_available = False
        if 'enable_ror_analysis' not in st.session_state:
            st.session_state.enable_ror_analysis = False

        self.system_stats = {
            'total_dois_processed': 0,
            'total_successful': 0,
            'total_failed': 0,
            'total_authors': 0,
            'total_requests': 0,
            'total_ref_dois': 0,
            'total_cite_dois': 0
        }

        # Check for resume availability
        self._check_resume_availability()

    def _check_resume_availability(self):
        """Check if there is saved progress for resuming"""
        stage, processed, remaining = self.cache_manager.load_progress()
        if stage and remaining:
            st.session_state.resume_available = True
            st.session_state.resume_stage = stage
            st.session_state.resume_remaining = remaining
        else:
            st.session_state.resume_available = False

    def _parse_dois(self, input_text: str) -> List[str]:
        if not input_text:
            return []

        # Remove DOI duplicates during parsing
        separators = [',', ';', '\n', '\t', '|']

        for sep in separators:
            if sep in input_text:
                parts = input_text.split(sep)
                break
        else:
            parts = input_text.split()

        dois = []
        for part in parts:
            doi = self._clean_doi(part)
            if doi and len(doi) > 5:
                dois.append(doi)

        # Remove duplicates and check for repeats
        unique_dois = []
        seen_dois = set()
        duplicate_dois = []
        
        for doi in dois:
            if doi not in seen_dois:
                seen_dois.add(doi)
                unique_dois.append(doi)
            else:
                duplicate_dois.append(doi)
        
        # Show duplicate warning
        if duplicate_dois:
            st.warning(f"⚠️ Duplicate DOI found ({len(duplicate_dois)}): {', '.join(duplicate_dois[:5])}{'...' if len(duplicate_dois) > 5 else ''}")
            st.info(f"Only unique DOI will be processed: {len(unique_dois)}")
        
        return unique_dois

    def _clean_doi(self, doi: str) -> str:
        if not doi or not isinstance(doi, str):
            return ""

        doi = doi.strip()
        prefixes = ['doi:', 'DOI:', 'https://doi.org/', 'http://doi.org/',
                   'https://dx.doi.org/', 'http://dx.doi.org/']

        for prefix in prefixes:
            if doi.lower().startswith(prefix.lower()):
                doi = doi[len(prefix):]

        return doi.strip()

    def process_dois(self, dois: List[str], num_workers: int = Config.DEFAULT_WORKERS,
                    progress_container=None, resume: bool = False, enable_ror: bool = False):
        """Main DOI processing function with resume support"""
        
        start_time = time.time()
        
        # Set ROR analysis flag
        self.excel_exporter.enable_ror_analysis = enable_ror
        st.session_state.enable_ror_analysis = enable_ror

        # Check resume possibility
        if resume and st.session_state.resume_available:
            stage = st.session_state.resume_stage
            remaining_dois = st.session_state.resume_remaining
            
            if progress_container:
                progress_container.text(f"🔄 Resuming processing from stage: {stage}")
            
            # Process remaining DOI depending on stage
            if stage == "analyzed":
                # Continue processing analyzed articles
                st.session_state.analyzed_results = self.doi_processor.process_doi_batch_with_resume(
                    remaining_dois, "analyzed", None, True, True, Config.BATCH_SIZE, 
                    progress_container, resume=True
                )
                
                # After completing analyzed, continue with reference
                all_ref_dois = self.doi_processor.collect_all_references(st.session_state.analyzed_results)
                if all_ref_dois:
                    ref_dois_to_analyze = all_ref_dois[:10000]
                    st.session_state.ref_results = self.doi_processor.process_doi_batch_with_resume(
                        ref_dois_to_analyze, "ref", None, True, True, Config.BATCH_SIZE,
                        progress_container, resume=False
                    )
                
                # Continue with citing
                all_cite_dois = self.doi_processor.collect_all_citations(st.session_state.analyzed_results)
                if all_cite_dois:
                    cite_dois_to_analyze = all_cite_dois[:10000]
                    st.session_state.citing_results = self.doi_processor.process_doi_batch_with_resume(
                        cite_dois_to_analyze, "citing", None, True, True, Config.BATCH_SIZE,
                        progress_container, resume=False
                    )
                    
            elif stage == "ref":
                # Continue processing reference articles
                st.session_state.ref_results = self.doi_processor.process_doi_batch_with_resume(
                    remaining_dois, "ref", None, True, True, Config.BATCH_SIZE,
                    progress_container, resume=True
                )
                
                # After completing reference, process citing
                all_cite_dois = self.doi_processor.collect_all_citations(st.session_state.analyzed_results)
                if all_cite_dois:
                    cite_dois_to_analyze = all_cite_dois[:10000]
                    st.session_state.citing_results = self.doi_processor.process_doi_batch_with_resume(
                        cite_dois_to_analyze, "citing", None, True, True, Config.BATCH_SIZE,
                        progress_container, resume=False
                    )
                    
            elif stage == "citing":
                # Continue processing citing articles
                st.session_state.citing_results = self.doi_processor.process_doi_batch_with_resume(
                    remaining_dois, "citing", None, True, True, Config.BATCH_SIZE,
                    progress_container, resume=True
                )
                
            # Reset resume flag
            st.session_state.resume_available = False
            
        else:
            # Normal processing from beginning
            if progress_container:
                progress_container.text("📚 Processing original DOI...")

            # Process original DOI
            st.session_state.analyzed_results = self.doi_processor.process_doi_batch_with_resume(
                dois, "analyzed", None, True, True, Config.BATCH_SIZE, progress_container, resume=False
            )

            # Update counters
            for doi, result in st.session_state.analyzed_results.items():
                if result.get('status') == 'success':
                    self.excel_exporter.update_counters(
                        result.get('references', []),
                        result.get('citations', []),
                        "analyzed"
                    )

            # Collect and process reference DOI
            if progress_container:
                progress_container.text("📎 Collecting reference DOI...")

            all_ref_dois = self.doi_processor.collect_all_references(st.session_state.analyzed_results)
            self.system_stats['total_ref_dois'] = len(all_ref_dois)

            if all_ref_dois:
                if progress_container:
                    progress_container.text(f"📎 Found {len(all_ref_dois)} reference DOI for analysis")

                ref_dois_to_analyze = all_ref_dois[:10000]  # Limit for performance

                st.session_state.ref_results = self.doi_processor.process_doi_batch_with_resume(
                    ref_dois_to_analyze, "ref", None, True, True, Config.BATCH_SIZE, progress_container, resume=False
                )

                for doi, result in st.session_state.ref_results.items():
                    if result.get('status') == 'success':
                        self.excel_exporter.update_counters(
                            result.get('references', []),
                            result.get('citations', []),
                            "ref"
                        )

            # Collect and process citation DOI
            if progress_container:
                progress_container.text("🔗 Collecting citation DOI...")

            all_cite_dois = self.doi_processor.collect_all_citations(st.session_state.analyzed_results)
            self.system_stats['total_cite_dois'] = len(all_cite_dois)

            if all_cite_dois:
                if progress_container:
                    progress_container.text(f"🔗 Found {len(all_cite_dois)} citation DOI for analysis")

                cite_dois_to_analyze = all_cite_dois[:10000]  # Limit for performance

                st.session_state.citing_results = self.doi_processor.process_doi_batch_with_resume(
                    cite_dois_to_analyze, "citing", None, True, True, Config.BATCH_SIZE, progress_container, resume=False
                )

                for doi, result in st.session_state.citing_results.items():
                    if result.get('status') == 'success':
                        self.excel_exporter.update_counters(
                            result.get('references', []),
                            result.get('citations', []),
                            "citing"
                        )

        # Retry failed DOI
        failed_stats = self.failed_tracker.get_stats()
        if failed_stats['total_failed'] > 0:
            if progress_container:
                progress_container.text("🔄 Retrying failed DOI...")
            retry_results = self.doi_processor.retry_failed_dois(self.failed_tracker)

            for doi, result in retry_results.items():
                if result.get('status') == 'success':
                    source_type = self.failed_tracker.sources.get(doi, 'retry')
                    if source_type == 'analyzed' and doi in self.failed_tracker.failed_dois:
                        st.session_state.analyzed_results[doi] = result
                    elif source_type == 'ref' and doi in self.failed_tracker.failed_dois:
                        st.session_state.ref_results[doi] = result
                    elif source_type == 'citing' and doi in self.failed_tracker.failed_dois:
                        st.session_state.citing_results[doi] = result

        processing_time = time.time() - start_time

        # Update statistics
        self.system_stats['total_dois_processed'] += len(dois)
        successful = sum(1 for r in st.session_state.analyzed_results.values() if r.get('status') == 'success')
        failed = len(dois) - successful

        st.session_state.processing_complete = True
        st.rerun()

        return {
            'processing_time': processing_time,
            'successful': successful,
            'failed': failed,
            'total_refs': self.system_stats['total_ref_dois'],
            'total_cites': self.system_stats['total_cite_dois']
        }

    def create_excel_report(self, progress_container=None):
        """Create Excel report"""
        # Update exporter with data
        self.excel_exporter.analyzed_results = st.session_state.analyzed_results
        self.excel_exporter.ref_results = st.session_state.ref_results
        self.excel_exporter.citing_results = st.session_state.citing_results
        
        # Set ROR analysis flag
        self.excel_exporter.enable_ror_analysis = st.session_state.enable_ror_analysis
        
        if progress_container:
            if st.session_state.enable_ror_analysis:
                progress_container.info("🔍 ROR analysis enabled. Organization data will be collected.")
            else:
                progress_container.info("ℹ️ ROR analysis disabled. Enable option to get ROR ID.")
    
        # Create report in memory
        excel_file = self.excel_exporter.create_comprehensive_report(
            st.session_state.analyzed_results,
            st.session_state.ref_results,
            st.session_state.citing_results,
            progress_container=progress_container,
            enable_ror=st.session_state.enable_ror_analysis
        )
    
        return excel_file

    def clear_data(self):
        """Clear all data"""
        st.session_state.analyzed_results = {}
        st.session_state.ref_results = {}
        st.session_state.citing_results = {}
        st.session_state.processing_complete = False
        st.session_state.resume_available = False
        st.session_state.enable_ror_analysis = False
        self.failed_tracker.clear()
        self.cache_manager.clear_progress()

# ============================================================================
# 🎛️ STREAMLIT INTERFACE (UPDATED)
# ============================================================================

def main():
    # System initialization
    if 'system' not in st.session_state:
        st.session_state.system = ArticleAnalyzerSystem()

    system = st.session_state.system

    # Sidebar for settings
    with st.sidebar:
        st.header("⚙️ Settings")
        
        # Parallelism settings
        num_workers = st.slider(
            "Number of threads",
            min_value=Config.MIN_WORKERS,
            max_value=Config.MAX_WORKERS,
            value=Config.DEFAULT_WORKERS,
            help="Number of parallel threads for DOI processing"
        )
        
        # ROR analysis settings
        enable_ror = st.checkbox(
            "Enable ROR analysis",
            value=False,
            help="Enable ROR ID search for affiliations (takes additional time)"
        )
        
        st.markdown("---")
        
        # Cache management
        st.subheader("🗂️ Cache Management")
        
        if st.button("Clear cache", type="secondary"):
            system.cache_manager.clear_all()
            st.success("Cache cleared!")
        
        # Show cache statistics
        cache_stats = system.cache_manager.get_stats()
        with st.expander("Cache statistics"):
            st.write(f"Efficiency: {cache_stats['hit_ratio']}%")
            st.write(f"API calls saved: {cache_stats['api_calls_saved']}")
            st.write(f"Cache size: {cache_stats['cache_size_mb']} MB")
        
        # Check resume availability
        if st.session_state.resume_available:
            st.markdown("---")
            st.subheader("🔄 Resume")
            st.info(f"Resume available from stage: {st.session_state.resume_stage}")
            st.write(f"Remaining DOI: {len(st.session_state.resume_remaining)}")

    # Main input area
    st.header("📝 DOI Input")
    
    doi_input = st.text_area(
        "Enter one or multiple DOI",
        height=150,
        placeholder="Enter DOI separated by comma, semicolon or new line.\n\nExamples:\n10.1038/nature12373\n10.1126/science.1252914, 10.1016/j.cell.2019.11.017",
        help="Can enter multiple DOI separated by commas, semicolons or line breaks"
    )
    
    col1, col2, col3, col4 = st.columns(4)
    
    with col1:
        process_btn = st.button("📊 Process DOI", type="primary", use_container_width=True)
    
    with col2:
        if st.session_state.resume_available:
            resume_btn = st.button("🔄 Resume", type="primary", use_container_width=True)
        else:
            resume_btn = None
            st.button("🔄 Resume", type="secondary", use_container_width=True, disabled=True)
    
    with col3:
        clear_btn = st.button("🧹 Clear data", type="secondary", use_container_width=True)
    
    with col4:
        # Check multiple conditions for button activation
        export_disabled = not (
            hasattr(st.session_state, 'processing_complete') and 
            st.session_state.processing_complete and
            hasattr(st.session_state, 'analyzed_results') and 
            st.session_state.analyzed_results
        )
        
        export_btn = st.button("💾 Export Excel", 
                             type="secondary", 
                             use_container_width=True,
                             disabled=export_disabled)
    
    # Handle button clicks
    if process_btn and doi_input:
        dois = system._parse_dois(doi_input)
        
        if not dois:
            st.error("❌ No valid DOI found. Check input format.")
        else:
            st.info(f"🔍 Found {len(dois)} valid DOI for processing")
            
            # Progress container
            progress_container = st.container()
            
            with progress_container:
                st.write("🚀 Starting processing...")
                
                # Start processing
                try:
                    results = system.process_dois(
                        dois, 
                        num_workers, 
                        progress_container,
                        resume=False,
                        enable_ror=enable_ror
                    )
                    
                    st.success(f"✅ Processing completed in {results['processing_time']:.1f} seconds")
                    
                    col1, col2, col3, col4 = st.columns(4)
                    with col1:
                        st.metric("Successful", results['successful'])
                    with col2:
                        st.metric("Errors", results['failed'])
                    with col3:
                        st.metric("Reference DOI", results['total_refs'])
                    with col4:
                        st.metric("Citation DOI", results['total_cites'])
                    
                    # Show failed DOI statistics
                    failed_stats = system.failed_tracker.get_stats()
                    if failed_stats['total_failed'] > 0:
                        with st.expander(f"❌ Failed DOI ({failed_stats['total_failed']})"):
                            st.write(f"• From analyzed: {failed_stats['analyzed_failed']}")
                            st.write(f"• From references: {failed_stats['ref_failed']}")
                            st.write(f"• From citations: {failed_stats['citing_failed']}")
                    
                    # Show examples of processed articles
                    with st.expander("📊 Examples of processed articles"):
                        successful_count = 0
                        for doi, result in st.session_state.analyzed_results.items():
                            if result.get('status') == 'success' and successful_count < 5:
                                pub_info = result['publication_info']
                                st.write(f"**{pub_info.get('title', '')[:80]}...**")
                                st.write(f"DOI: {doi}")
                                st.write(f"Journal: {pub_info.get('journal', '')}")
                                st.write(f"Year: {pub_info.get('year', '')}")
                                st.write("---")
                                successful_count += 1
                
                except Exception as e:
                    st.error(f"❌ Processing error: {str(e)}")
                    st.info("⚠️ Processing progress saved. Can resume from interruption point.")
    
    elif resume_btn and st.session_state.resume_available:
        # Resume processing
        progress_container = st.container()
        
        with progress_container:
            st.write(f"🔄 Resuming processing from stage: {st.session_state.resume_stage}")
            
            try:
                results = system.process_dois(
                    [],  # Empty list as using saved DOI
                    num_workers,
                    progress_container,
                    resume=True,
                    enable_ror=enable_ror
                )
                
                st.success(f"✅ Processing resumed and completed")
                
                col1, col2, col3, col4 = st.columns(4)
                with col1:
                    st.metric("Successful", results['successful'])
                with col2:
                    st.metric("Errors", results['failed'])
                with col3:
                    st.metric("Reference DOI", results['total_refs'])
                with col4:
                    st.metric("Citation DOI", results['total_cites'])
                    
            except Exception as e:
                st.error(f"❌ Resume processing error: {str(e)}")
    
    elif process_btn and not doi_input:
        st.warning("⚠️ Enter DOI for processing")
    
    if clear_btn:
        system.clear_data()
        st.success("✅ Data cleared")
        st.rerun()
    
    if export_btn and st.session_state.processing_complete:
        with st.spinner("📊 Creating Excel report..."):
            try:
                # Create report
                excel_file = system.create_excel_report()
                
                # Create filename
                timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
                filename = f"articles_analysis_{timestamp}.xlsx"
                
                # Provide file for download
                st.download_button(
                    label="⬇️ Download Excel file",
                    data=excel_file,
                    file_name=filename,
                    mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet"
                )
                
                st.success("✅ Excel report created and ready for download")
                
            except Exception as e:
                st.error(f"❌ Report creation error: {str(e)}")
    
    # Show statistics if there is processed data
    if st.session_state.processing_complete:
        st.header("📈 Processing Statistics")
        
        successful = sum(1 for r in st.session_state.analyzed_results.values() if r.get('status') == 'success')
        total = len(st.session_state.analyzed_results)
        
        col1, col2, col3 = st.columns(3)
        
        with col1:
            st.metric(
                "Analyzed articles",
                f"{successful}/{total}",
                f"{successful/total*100:.1f}%" if total > 0 else "0%"
            )
        
        with col2:
            ref_success = sum(1 for r in st.session_state.ref_results.values() if r.get('status') == 'success')
            ref_total = len(st.session_state.ref_results)
            st.metric(
                "Reference articles",
                f"{ref_success}/{ref_total}" if ref_total > 0 else "0",
                f"{ref_success/ref_total*100:.1f}%" if ref_total > 0 else "0%"
            )
        
        with col3:
            cite_success = sum(1 for r in st.session_state.citing_results.values() if r.get('status') == 'success')
            cite_total = len(st.session_state.citing_results)
            st.metric(
                "Citing articles",
                f"{cite_success}/{cite_total}" if cite_total > 0 else "0",
                f"{cite_success/cite_total*100:.1f}%" if cite_total > 0 else "0%"
            )
        
        # Detailed statistics
        with st.expander("📊 Detailed statistics"):
            # Author statistics
            total_authors = 0
            for result in st.session_state.analyzed_results.values():
                if result.get('status') == 'success':
                    total_authors += len(result.get('authors', []))
            
            # Reference and citation statistics
            total_refs = 0
            total_cites = 0
            for result in st.session_state.analyzed_results.values():
                if result.get('status') == 'success':
                    total_refs += len(result.get('references', []))
                    total_cites += len(result.get('citations', []))
            
            st.write(f"**Total authors:** {total_authors}")
            st.write(f"**Total references:** {total_refs}")
            st.write(f"**Total citations:** {total_cites}")
            st.write(f"**Unique reference DOI:** {len(system.excel_exporter.references_counter)}")
            st.write(f"**Unique citation DOI:** {len(system.excel_exporter.citations_counter)}")
            
            # Cache statistics
            cache_stats = system.cache_manager.get_stats()
            st.write(f"**Cache efficiency:** {cache_stats['hit_ratio']}%")
            st.write(f"**API calls saved:** {cache_stats['api_calls_saved']}")

# ============================================================================
# 🏃‍♂️ RUN APPLICATION
# ============================================================================

if __name__ == "__main__":
    main()





