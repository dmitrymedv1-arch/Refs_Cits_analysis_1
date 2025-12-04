# -*- coding: utf-8 -*-
"""📚 Анализатор научных статей по DOI с умным кэшированием и экспортом в Excel - Streamlit версия"""

# ============================================================================
# 📦 ИМПОРТЫ И НАСТРОЙКА
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
import math
import networkx as nx
from sklearn.ensemble import IsolationForest
from sklearn.preprocessing import StandardScaler
import numpy as np
import plotly.graph_objects as go
import plotly.express as px
import matplotlib.pyplot as plt
import seaborn as sns
from io import BytesIO
import base64
import tempfile

# ============================================================================
# ⚙️ КОНФИГУРАЦИЯ
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
    
    # Streamlit-specific cache directory
    CACHE_DIR = os.path.join(tempfile.gettempdir(), "article_analyzer_cache")
    TTL_HOURS = 24
    MAX_CACHE_SIZE_MB = 50
    
    MIN_WORKERS = 1
    MAX_WORKERS = 10
    DEFAULT_WORKERS = 4
    
    BATCH_SIZE = 50
    
    TOP_PERCENTILE_FOR_DEEP_ANALYSIS = 10
    MIN_CITATIONS_FOR_DEEP_ANALYSIS = 10
    
    # Пороговые значения для анализа неэтичных практик
    QUICK_CHECK_THRESHOLDS = {
        'journal_concentration': 0.7,  # >70% из одного журнала
        'author_self_citation': 0.3,   # >30% с общими авторами
        'affiliation_self_citation': 0.6,  # >60% из той же аффилиации
        'single_country': 0.8,         # >80% из одной страны
        'citation_velocity': 20,       # >20 цитирований в год
        'first_year_share': 0.5        # >50% в первый год
    }
    
    MEDIUM_INSIGHT_THRESHOLDS = {
        'first_two_years': 0.7,        # >70% за первые 2 года
        'top_journal_share': 0.6,      # >60% из топ-1 журнала
        'cluster_coefficient': 0.8,    # коэффициент кластеризации >0.8
        'geographic_bias': 0.9         # географический bias >0.9
    }
    
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
# 🗂️ КЛАСС УМНОГО КЭШИРОВАНИЯ (УЛУЧШЕННЫЙ)
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
        
        # Кэш для результатов анализа неэтичных практик
        self.ethical_analysis_cache = {
            'quick_checks': {},
            'medium_insights': {},
            'deep_analysis': {},
            'citing_relationships': {}
        }
        
        if not os.path.exists(cache_dir):
            os.makedirs(cache_dir, exist_ok=True)
            
        self._clean_expired_cache()
        
        self._load_popular_dois()
    
    def _get_cache_key(self, source: str, identifier: str) -> str:
        key_str = f"v3:{source}:{identifier}"
        return hashlib.sha256(key_str.encode()).hexdigest()[:32]
    
    def _get_cache_path(self, key: str) -> str:
        return os.path.join(self.cache_dir, f"{key}.pkl")
    
    def _get_cache_metadata_path(self, key: str) -> str:
        return os.path.join(self.cache_dir, f"{key}_meta.json")
    
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
            st.warning(f"⚠️ Ошибка очистки кэша: {e}")
    
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
            st.warning(f"⚠️ Ошибка удаления старых элементов кэша: {e}")
    
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
    
    def set(self, source: str, identifier: str, data: Any, category: str = "default"):
        key = self._get_cache_key(source, identifier)
        cache_path = self._get_cache_path(key)
        meta_path = self._get_cache_metadata_path(key)
        
        cache_entry = {
            'timestamp': time.time(),
            'source': source,
            'identifier': identifier,
            'data': data,
            'category': category
        }
        
        try:
            with open(cache_path, 'wb') as f:
                pickle.dump(cache_entry, f, protocol=pickle.HIGHEST_PROTOCOL)
            
            metadata = {
                'category': category,
                'created': datetime.now().isoformat(),
                'source': source,
                'identifier_hash': hashlib.md5(str(identifier).encode()).hexdigest()
            }
            
            with open(meta_path, 'w') as mf:
                json.dump(metadata, mf, indent=2)
            
            memory_key = f"{category}:{key}"
            if len(self.memory_cache) >= self.max_memory_items:
                self.memory_cache.popitem(last=False)
            
            self.memory_cache[memory_key] = data
            
            self.stats['api_calls_saved'] += 1
            
        except Exception as e:
            st.warning(f"⚠️ Ошибка сохранения в кэш: {e}")
    
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
                st.info(f"✅ Загружено {len(self.popular_cache)} популярных DOI")
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
            self.ethical_analysis_cache = {
                'quick_checks': {}, 'medium_insights': {}, 'deep_analysis': {}, 'citing_relationships': {}
            }
            self.stats = {k: 0 for k in self.stats.keys()}
            
            st.success("✅ Кэш полностью очищен")
            
        except Exception as e:
            st.error(f"⚠️ Ошибка очистки кэша: {e}")
    
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
    
    # Методы для кэширования анализа неэтичных практик
    def get_ethical_analysis(self, analysis_type: str, doi: str) -> Optional[Dict]:
        if analysis_type in self.ethical_analysis_cache and doi in self.ethical_analysis_cache[analysis_type]:
            return self.ethical_analysis_cache[analysis_type][doi]
        return None
    
    def set_ethical_analysis(self, analysis_type: str, doi: str, data: Dict):
        if analysis_type not in self.ethical_analysis_cache:
            self.ethical_analysis_cache[analysis_type] = {}
        self.ethical_analysis_cache[analysis_type][doi] = {
            'data': data,
            'timestamp': time.time()
        }
    
    def clear_ethical_analysis(self, analysis_type: str = None):
        if analysis_type:
            if analysis_type in self.ethical_analysis_cache:
                self.ethical_analysis_cache[analysis_type].clear()
        else:
            for analysis in self.ethical_analysis_cache:
                self.ethical_analysis_cache[analysis].clear()

# ============================================================================
# 🚀 КЛАСС АДАПТИВНЫХ ЗАДЕРЖЕК
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
# 📊 КЛАСС МОНИТОРИНГА ПРОГРЕССА (НОВЫЙ) - Адаптированный для Streamlit
# ============================================================================

class ProgressMonitor:
    def __init__(self, total_items: int, stage_name: str = "Обработка", progress_bar=None, status_text=None):
        self.total_items = total_items
        self.processed_items = 0
        self.start_time = time.time()
        self.stage_name = stage_name
        self.last_progress_time = self.start_time
        self.processing_speeds = []
        
        self.checkpoint_times = []
        self.checkpoint_items = []
        
        self.stats = {
            'success': 0,
            'failed': 0,
            'cached': 0,
            'skipped': 0
        }
        
        # Streamlit progress bar
        self.progress_bar = progress_bar
        self.status_text = status_text  # Теперь принимаем status_text как параметр
        
        # Если нет прогресс-бара, создаем информационное сообщение
        if self.progress_bar is None:
            st.info(f"📊 {stage_name}: начата обработка {total_items} элементов")
    
    def update(self, count: int = 1, item_type: str = None):
        self.processed_items += count
        
        if item_type:
            if item_type in self.stats:
                self.stats[item_type] += count
            else:
                self.stats[item_type] = count
        
        # Update Streamlit progress bar if available
        if self.progress_bar and self.total_items > 0:
            progress_percent = (self.processed_items / self.total_items) * 100
            
            # Обновляем прогресс бар
            self.progress_bar.progress(progress_percent / 100.0)
            
            # Обновляем текстовый статус
            if self.status_text:
                elapsed = time.time() - self.start_time
                if elapsed > 0:
                    speed = self.processed_items / elapsed
                    items_per_min = speed * 60
                    
                    remaining_items = self.total_items - self.processed_items
                    if speed > 0:
                        eta_seconds = remaining_items / speed
                        eta_str = self._format_time(eta_seconds)
                    else:
                        eta_str = "расчет..."
                    
                    stats_str = ""
                    for stat_type, count in self.stats.items():
                        if count > 0:
                            stats_str += f", {stat_type}: {count}"
                    
                    # Обновляем текст статуса
                    self.status_text.text(
                        f"{self.stage_name}: {self.processed_items}/{self.total_items} "
                        f"({progress_percent:.1f}%), "
                        f"скорость: {items_per_min:.1f} DOI/мин, "
                        f"осталось: {eta_str}{stats_str}"
                    )
    
    def _format_time(self, seconds: float) -> str:
        if seconds < 60:
            return f"{seconds:.0f} сек"
        elif seconds < 3600:
            minutes = seconds / 60
            return f"{minutes:.0f} мин"
        else:
            hours = seconds / 3600
            return f"{hours:.1f} ч"
    
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
        
        if self.progress_bar:
            self.progress_bar.progress(1.0)
        
        st.success(f"✅ {self.stage_name} завершена!")
        st.info(f"Всего элементов: {self.total_items}")
        st.info(f"Обработано: {self.processed_items} ({progress_percent:.1f}%)")
        st.info(f"Затраченное время: {self._format_time(elapsed)}")
        st.info(f"Скорость обработки: {summary['speed_per_min']:.1f} DOI/мин")
        
        for stat_type, count in self.stats.items():
            if count > 0:
                st.info(f"{stat_type.capitalize()}: {count}")
        
        return summary

# ============================================================================
# 📝 КЛАСС ТРЕКИНГА НЕУДАЧНЫХ DOI (НОВЫЙ)
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
                relationship_info = f"Источник: {info['original_doi']}"
            elif info['related_dois']:
                relationship_info = f"Связан с: {', '.join(info['related_dois'][:3])}"
                if len(info['related_dois']) > 3:
                    relationship_info += f"... (еще {len(info['related_dois']) - 3})"
            
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
# 🌐 КЛАСС КЛИЕНТОВ API
# ============================================================================

class APIClient:
    def __init__(self, cache_manager: SmartCacheManager, delay_manager: AdaptiveDelayManager):
        self.cache = cache_manager
        self.delay = delay_manager
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'ArticleAnalyzer/3.0 (streamlit-app@example.com)',
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
    
    def fetch_citations(self, doi: str, max_pages: int = 3) -> List[str]:
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
                'per-page': 100,
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
    
    def _clean_doi(self, doi: str) -> str:
        if not doi or not isinstance(doi, str):
            return ""
        
        doi = doi.strip()
        prefixes = ['doi:', 'DOI:', 'https://doi.org/', 'http://doi.org/', 'https://dx.doi.org/', 'http://dx.doi.org/']
        
        for prefix in prefixes:
            if doi.lower().startswith(prefix.lower()):
                doi = doi[len(prefix):]
        
        return doi.strip()

class RORClient:
    def __init__(self, cache_manager: SmartCacheManager):
        self.cache = cache_manager
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'ArticleAnalyzer-ROR/3.0 (streamlit-app@example.com)',
            'Accept': 'application/json'
        })
        self.last_request_time = 0
        self.min_delay = 0.3

    def _respect_delay(self):
        elapsed = time.time() - self.last_request_time
        if elapsed < self.min_delay:
            time.sleep(self.min_delay - elapsed)
        self.last_request_time = time.time()

    def search_organization(self, query: str, category: str = "summary") -> Dict[str, str]:
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
# 🛠️ КЛАСС ОБРАБОТКИ ДАННЫХ
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
        for author in authors:
            if author.get('orcid'):
                orcid_url = self._format_orcid_id(author['orcid'])
                if orcid_url:
                    orcid_urls.append(orcid_url)
        
        pages_field = pub_info['pages']
        if not pages_field and pub_info['article_number']:
            pages_field = f"Article {pub_info['article_number']}"
        
        quick_insights = self._extract_quick_insights(
            authors, countries, references, citations, pub_info
        )
        
        return {
            'doi': doi,
            'publication_info': pub_info,
            'authors': authors,
            'countries': country_codes,
            'orcid_urls': orcid_urls,
            'references': references,
            'citations': citations,
            'pages_formatted': pages_field,
            'status': 'success',
            'quick_insights': quick_insights
        }
    
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
            
            # Улучшенный парсинг даты из Crossref
            pub_date = None
            if 'created' in msg and 'date-parts' in msg['created']:
                created_date = msg.get('created', {})
                if 'date-parts' in created_date and created_date['date-parts']:
                    pub_date = created_date['date-parts'][0]

            # Если не нашли в created, тогда используем license как fallback
            if not pub_date and 'license' in msg:
                for license_item in msg['license']:
                    if isinstance(license_item, dict) and 'start' in license_item:
                        start_date = license_item.get('start', {})
                        if 'date-parts' in start_date and start_date['date-parts']:
                            pub_date = start_date['date-parts'][0]
                            break
            
            # Если не нашли в license, ищем в created
            if not pub_date and 'created' in msg:
                created_date = msg.get('created', {})
                if 'date-parts' in created_date and created_date['date-parts']:
                    pub_date = created_date['date-parts'][0]
            
            # Если не нашли в created, используем старую логику
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
                        'orcid': author_display.get('orcid', '')
                    }
                    
                    institutions = authorship.get('institutions', [])
                    if institutions:
                        for inst in institutions:
                            if inst and isinstance(inst, dict):
                                display_name = inst.get('display_name')
                                if display_name:
                                    clean_aff = self._clean_affiliation(display_name)
                                    if clean_aff:
                                        author_info['affiliation'].append(clean_aff)
                                
                                country_code = inst.get('country_code')
                                if country_code:
                                    countries.append(country_code)
                    
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
                            'orcid': author_obj.get('ORCID', '')
                        }
                        
                        affiliations = author_obj.get('affiliation', [])
                        if affiliations:
                            for affil in affiliations:
                                if affil and isinstance(affil, dict):
                                    affil_name = affil.get('name')
                                    if affil_name:
                                        clean_aff = self._clean_affiliation(affil_name)
                                        if clean_aff:
                                            author_info['affiliation'].append(clean_aff)
                        
                        authors.append(author_info)
            except Exception as e:
                st.warning(f"⚠️ Crossref author extraction error: {e}")
        
        return authors, list(set(countries))
    
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
# 🎯 КЛАСС ОПТИМИЗИРОВАННОЙ ОБРАБОТКИ DOI (НОВЫЙ) - Адаптированный для Streamlit
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
    
    def process_doi_batch(self, dois: List[str], source_type: str = "analyzed", 
                         original_doi: str = None, fetch_refs: bool = True, 
                         fetch_cites: bool = True, batch_size: int = Config.BATCH_SIZE,
                         progress_container=None) -> Dict[str, Dict]:
        
        results = {}
        total_batches = (len(dois) + batch_size - 1) // batch_size
        
        if progress_container:
            progress_container.info(f"🔧 Обработка {len(dois)} DOI (источник: {source_type})")
            progress_container.info(f"📦 Разбито на {total_batches} пачек по {batch_size} DOI")
        
        # Создаем прогресс-бар для Streamlit
        progress_bar = None
        status_text = None
        if progress_container:
            progress_bar = progress_container.progress(0)
            status_text = progress_container.empty()
        
        # Передаем и progress_bar и status_text в ProgressMonitor
        monitor = ProgressMonitor(len(dois), f"Обработка {source_type}", 
                                 progress_bar=progress_bar, status_text=status_text)
        
        for batch_idx in range(0, len(dois), batch_size):
            batch = dois[batch_idx:batch_idx + batch_size]
            batch_results = self._process_single_batch(
                batch, source_type, original_doi, True, True
            )
            
            results.update(batch_results)
            
            monitor.update(len(batch), 'processed')
            
            batch_success = sum(1 for r in batch_results.values() if r.get('status') == 'success')
            if progress_container:
                progress_container.info(f"Пачка {batch_idx//batch_size + 1}/{total_batches}: "
                                      f"{batch_success}/{len(batch)} успешно, "
                                      f"{self.delay.get_delay():.2f}s задержка")
        
        monitor.complete()
        
        successful = sum(1 for r in results.values() if r.get('status') == 'success')
        failed = len(dois) - successful
        
        self.stats['total_processed'] += len(dois)
        self.stats['successful'] += successful
        self.stats['failed'] += failed
        
        return results
    
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
                        'error': f"Таймаут обработки: {str(e)}"
                    }
        
        return results
    
    def _process_single_doi_wrapper(self, doi: str, source_type: str, 
                                   original_doi: str, fetch_refs: bool, fetch_cites: bool) -> Dict:
        try:
            return self._process_single_doi_optimized(
                doi, source_type, original_doi, True, True
            )
        except Exception as e:
            self._handle_processing_error(doi, str(e), source_type, original_doi)
            return {
                'doi': doi,
                'status': 'failed',
                'error': f"Ошибка обработки: {str(e)}"
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
            error_msg = f"Ошибка получения данных: {str(e)}"
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
            error_msg = f"Ошибки API: Crossref - {crossref_error}, OpenAlex - {openalex_error}"
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
            cites_openalex = self.openalex_client.fetch_citations(doi)
            cites_crossref = self.crossref_client.fetch_citations(doi)
            
            cites_openalex = cites_openalex if isinstance(cites_openalex, list) else []
            cites_crossref = cites_crossref if isinstance(cites_crossref, list) else []
            
            citations = list(set(cites_openalex + cites_crossref))
            
            if citations:
                self.citation_relationships[doi] = citations
        except Exception as e:
            st.warning(f"⚠️ Error fetching citations for {doi}: {e}")
        
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
    
    def retry_failed_dois(self, failed_tracker: FailedDOITracker, max_retries: int = 1,
                         progress_container=None) -> Dict[str, Dict]:
        retry_results = {}
        
        rate_limit_dois = []
        for doi, info in failed_tracker.failed_dois.items():
            if 'Rate limit exceeded' in info.get('error', ''):
                rate_limit_dois.append(doi)
        
        if not rate_limit_dois:
            return retry_results
        
        if progress_container:
            progress_container.info(f"\n🔄 Повторная обработка {len(rate_limit_dois)} DOI с rate limiting ошибками")
        
        original_delay = self.delay.current_delay
        self.delay.current_delay = min(Config.MAX_DELAY, original_delay * 1.5)
        
        if progress_container:
            progress_container.info(f"Увеличена задержка: {original_delay:.3f}s -> {self.delay.current_delay:.3f}s")
        
        retry_results = self.process_doi_batch(
            rate_limit_dois, "retry", None, True, True, Config.BATCH_SIZE, progress_container
        )
        
        self.delay.current_delay = original_delay
        
        successful_retries = sum(1 for r in retry_results.values() if r.get('status') == 'success')
        
        if progress_container:
            progress_container.info(f"Успешно повторно обработано: {successful_retries}/{len(rate_limit_dois)}")
        
        return retry_results

# ============================================================================
# 🔍 КЛАСС ИЕРАРХИЧЕСКОГО АНАЛИЗА ДАННЫХ (НОВЫЙ)
# ============================================================================

class HierarchicalDataAnalyzer:
    def __init__(self, cache_manager: SmartCacheManager, data_processor: DataProcessor,
                 doi_processor: OptimizedDOIProcessor):
        self.cache = cache_manager
        self.processor = data_processor
        self.doi_processor = doi_processor
        
        # Иерархические уровни данных
        self.data_levels = {
            'level_0': set(),  # DOI и базовые метаданные
            'level_1': set(),  # + авторы, аффилиации, годы
            'level_2': set(),  # + полные метаданные цитирующих
            'level_3': set()   # + сетевой анализ и ML
        }
        
        # Временные метрики для анализа
        self.citation_timestamps = defaultdict(list)
        self.journal_citation_counts = defaultdict(Counter)
        self.author_citation_network = defaultdict(set)
        self.affiliation_citation_network = defaultdict(set)
        
        # ML модели для аномалий
        self.isolation_forest = None
        self.scaler = StandardScaler()
        
    def analyze_quick_checks(self, analyzed_results: Dict[str, Dict], 
                            citing_results: Dict[str, Dict]) -> List[Dict]:
        """Быстрые проверки (5-10 секунд на статью)"""
        quick_checks = []
        
        for doi, result in analyzed_results.items():
            if result.get('status') != 'success':
                continue
            
            # Получаем цитирующие статьи для этой DOI
            citing_dois = result.get('citations', [])
            citing_data = {}
            for cite_doi in citing_dois:
                if cite_doi in citing_results and citing_results[cite_doi].get('status') == 'success':
                    citing_data[cite_doi] = citing_results[cite_doi]
            
            # Анализ
            analysis = self._perform_quick_check_analysis(doi, result, citing_data)
            quick_checks.append(analysis)
            
            # Кэшируем результаты
            self.cache.set_ethical_analysis('quick_checks', doi, analysis)
        
        return sorted(quick_checks, key=lambda x: x['Quick_Risk_Score'], reverse=True)
    
    def _perform_quick_check_analysis(self, doi: str, result: Dict, 
                                     citing_data: Dict[str, Dict]) -> Dict:
        """Выполняет быстрые проверки для одной статьи"""
        
        pub_info = result['publication_info']
        authors = result.get('authors', [])
        analyzed_countries = result.get('countries', [])
        
        # 1. Journal Citation Concentration
        journal_concentration = self._calculate_journal_concentration(citing_data)
        
        # 2. Author Self-Citation Rate
        author_self_citation = self._calculate_author_self_citation(authors, citing_data)
        
        # 3. Affiliation Self-Citation
        affiliation_self_citation = self._calculate_affiliation_self_citation(authors, citing_data)
        
        # 4. Single Country Concentration
        single_country = self._calculate_single_country_concentration(citing_data, analyzed_countries)
        
        # 5. Citation Velocity
        citation_velocity = self._calculate_citation_velocity(result, citing_data)
        
        # 6. First Year Share
        first_year_share = self._calculate_first_year_share(result, citing_data)
        
        # 7. Future Citations
        future_citations = self._check_future_citations(result, citing_data)
        
        # Подсчет красных флагов
        red_flags = 0
        flags = []
        
        if journal_concentration > Config.QUICK_CHECK_THRESHOLDS['journal_concentration']:
            red_flags += 1
            flags.append(f"Journal concentration: {journal_concentration:.1%}")
        
        if author_self_citation > Config.QUICK_CHECK_THRESHOLDS['author_self_citation']:
            red_flags += 1
            flags.append(f"Author self-citation: {author_self_citation:.1%}")
        
        if affiliation_self_citation > Config.QUICK_CHECK_THRESHOLDS['affiliation_self_citation']:
            red_flags += 1
            flags.append(f"Affiliation self-citation: {affiliation_self_citation:.1%}")
        
        if single_country > Config.QUICK_CHECK_THRESHOLDS['single_country']:
            red_flags += 1
            flags.append(f"Single country: {single_country:.1%}")
        
        if citation_velocity > Config.QUICK_CHECK_THRESHOLDS['citation_velocity']:
            red_flags += 1
            flags.append(f"Citation velocity: {citation_velocity:.1f}/year")
        
        if first_year_share > Config.QUICK_CHECK_THRESHOLDS['first_year_share']:
            red_flags += 1
            flags.append(f"First year share: {first_year_share:.1%}")
        
        if future_citations > 0:
            red_flags += 1
            flags.append(f"Future citations: {future_citations}")
        
        # Расчет риска
        quick_risk_score = self._calculate_quick_risk_score(
            journal_concentration, author_self_citation, affiliation_self_citation,
            single_country, citation_velocity, first_year_share, future_citations
        )
        
        # Рекомендуемое действие
        recommended_action = self._determine_recommended_action(quick_risk_score, red_flags)
        
        return {
            'DOI': doi,
            'Title': pub_info.get('title', '')[:50] + ('...' if len(pub_info.get('title', '')) > 50 else ''),
            'Quick_Risk_Score': quick_risk_score,
            'Red_Flags': red_flags,
            'Flag_1_Journal_Concentration': journal_concentration > Config.QUICK_CHECK_THRESHOLDS['journal_concentration'],
            'Flag_2_Author_Self_Citation': author_self_citation > Config.QUICK_CHECK_THRESHOLDS['author_self_citation'],
            'Flag_3_Affiliation_Self_Citation': affiliation_self_citation > Config.QUICK_CHECK_THRESHOLDS['affiliation_self_citation'],
            'Flag_4_Single_Country': single_country > Config.QUICK_CHECK_THRESHOLDS['single_country'],
            'Flag_5_Citation_Velocity': citation_velocity > Config.QUICK_CHECK_THRESHOLDS['citation_velocity'],
            'Flag_6_First_Year_Share': first_year_share > Config.QUICK_CHECK_THRESHOLDS['first_year_share'],
            'Flag_7_Future_Citations': future_citations > 0,
            'Future_Citations_Count': future_citations,
            'Journal_Concentration_Rate': round(journal_concentration * 100, 1),
            'Author_Self_Citation_Rate': round(author_self_citation * 100, 1),
            'Affiliation_Self_Citation_Rate': round(affiliation_self_citation * 100, 1),
            'Single_Country_Percent': round(single_country * 100, 1),
            'Citation_Velocity_Annual': round(citation_velocity, 1),
            'First_Year_Share_Percent': round(first_year_share * 100, 1),
            'Recommended_Action': recommended_action,
            'Flags_Details': '; '.join(flags) if flags else 'None'
        }
    
    def _calculate_journal_concentration(self, citing_data: Dict[str, Dict]) -> float:
        """Рассчитывает концентрацию цитирований по журналам"""
        if not citing_data:
            return 0.0
        
        journal_counter = Counter()
        for cite_result in citing_data.values():
            journal = cite_result.get('publication_info', {}).get('journal', '')
            if journal:
                journal_counter[journal] += 1
        
        if not journal_counter:
            return 0.0
        
        total_citations = sum(journal_counter.values())
        top_journal_count = journal_counter.most_common(1)[0][1]
        
        return top_journal_count / total_citations
    
    def _calculate_author_self_citation(self, analyzed_authors: List[Dict], 
                                       citing_data: Dict[str, Dict]) -> float:
        """Рассчитывает процент self-citation по авторам"""
        if not citing_data or not analyzed_authors:
            return 0.0
        
        analyzed_author_names = {author['name'] for author in analyzed_authors}
        total_citations = len(citing_data)
        self_citations = 0
        
        for cite_result in citing_data.values():
            citing_authors = cite_result.get('authors', [])
            citing_author_names = {author['name'] for author in citing_authors}
            
            # Проверяем наличие общих авторов
            common_authors = analyzed_author_names.intersection(citing_author_names)
            if common_authors:
                self_citations += 1
        
        return self_citations / total_citations if total_citations > 0 else 0.0
    
    def _calculate_affiliation_self_citation(self, analyzed_authors: List[Dict], 
                                           citing_data: Dict[str, Dict]) -> float:
        """Рассчитывает процент self-citation по аффилиациям"""
        if not citing_data or not analyzed_authors:
            return 0.0
        
        # Собираем аффилиации анализируемой статьи
        analyzed_affiliations = set()
        for author in analyzed_authors:
            analyzed_affiliations.update(author.get('affiliation', []))
        
        if not analyzed_affiliations:
            return 0.0
        
        total_citations = len(citing_data)
        self_citations = 0
        
        for cite_result in citing_data.values():
            citing_authors = cite_result.get('authors', [])
            citing_affiliations = set()
            
            for author in citing_authors:
                citing_affiliations.update(author.get('affiliation', []))
            
            # Проверяем наличие общих аффилиаций
            common_affiliations = analyzed_affiliations.intersection(citing_affiliations)
            if common_affiliations:
                self_citations += 1
        
        return self_citations / total_citations if total_citations > 0 else 0.0
    
    def _calculate_single_country_concentration(self, citing_data: Dict[str, Dict], 
                                              analyzed_countries: List[str]) -> float:
        """Рассчитывает концентрацию цитирований по странам"""
        if not citing_data:
            return 0.0
        
        country_counter = Counter()
        for cite_result in citing_data.values():
            countries = cite_result.get('countries', [])
            for country in countries:
                if country:
                    country_counter[country] += 1
        
        if not country_counter:
            return 0.0
        
        total_citations = sum(country_counter.values())
        top_country_count = country_counter.most_common(1)[0][1]
        
        return top_country_count / total_citations
    
    def _calculate_citation_velocity(self, result: Dict, citing_data: Dict[str, Dict]) -> float:
        """Рассчитывает скорость цитирования (цитирований в год)"""
        if not citing_data:
            return 0.0
        
        pub_year_str = result.get('publication_info', {}).get('year', '')
        if not pub_year_str:
            return 0.0
        
        try:
            pub_year = int(pub_year_str)
            current_year = datetime.now().year
            years_passed = max(1, current_year - pub_year)
            
            return len(citing_data) / years_passed
        except:
            return 0.0
    
    def _calculate_first_year_share(self, result: Dict, citing_data: Dict[str, Dict]) -> float:
        """Рассчитывает долю цитирований в первый год"""
        if not citing_data:
            return 0.0
        
        pub_year_str = result.get('publication_info', {}).get('year', '')
        if not pub_year_str:
            return 0.0
        
        try:
            pub_year = int(pub_year_str)
            first_year_citations = 0
            total_citations = len(citing_data)
            
            for cite_doi, cite_result in citing_data.items():
                cite_year_str = cite_result.get('publication_info', {}).get('year', '')
                if cite_year_str:
                    try:
                        cite_year = int(cite_year_str)
                        if cite_year == pub_year:
                            first_year_citations += 1
                    except:
                        pass
            
            return first_year_citations / total_citations if total_citations > 0 else 0.0
        except:
            return 0.0
    
    def _check_future_citations(self, result: Dict, citing_data: Dict[str, Dict]) -> int:
        """Проверяет цитирования из будущего"""
        if not citing_data:
            return 0
        
        pub_date_str = result.get('publication_info', {}).get('publication_date', '')
        if not pub_date_str:
            return 0
        
        try:
            pub_date = datetime.strptime(pub_date_str[:10], '%Y-%m-%d')
            future_citations = 0
            
            for cite_result in citing_data.values():
                cite_date_str = cite_result.get('publication_info', {}).get('publication_date', '')
                if cite_date_str:
                    try:
                        cite_date = datetime.strptime(cite_date_str[:10], '%Y-%m-%d')
                        if cite_date < pub_date:
                            future_citations += 1
                    except:
                        pass
            
            return future_citations
        except:
            return 0
    
    def _calculate_quick_risk_score(self, *metrics) -> int:
        """Рассчитывает общий скоринговый риск"""
        score = 0
        
        # Весовые коэффициенты для разных метрик
        weights = [20, 15, 15, 10, 10, 15, 15]
        
        for metric, weight in zip(metrics, weights):
            if isinstance(metric, float):
                score += int(metric * weight)
            elif isinstance(metric, int):
                score += metric * 5
        
        return min(100, score)
    
    def _determine_recommended_action(self, risk_score: int, red_flags: int) -> str:
        """Определяет рекомендуемое действие на основе оценки риска"""
        if risk_score > 80 or red_flags >= 5:
            return "IMMEDIATE INVESTIGATION"
        elif risk_score > 60 or red_flags >= 3:
            return "DETAILED REVIEW REQUIRED"
        elif risk_score > 40 or red_flags >= 2:
            return "MONITOR AND REVIEW"
        elif risk_score > 20:
            return "MINOR REVIEW SUGGESTED"
        else:
            return "ETHICALLY ACCEPTABLE"
    
    def analyze_medium_insights(self, analyzed_results: Dict[str, Dict], 
                               citing_results: Dict[str, Dict]) -> List[Dict]:
        """Средние инсайты (15-30 секунд на статью)"""
        medium_insights = []
        
        # Собираем статистику по журналам для сравнения
        journal_stats = self._collect_journal_statistics(analyzed_results, citing_results)
        
        for doi, result in analyzed_results.items():
            if result.get('status') != 'success':
                continue
            
            # Получаем цитирующие статьи
            citing_dois = result.get('citations', [])
            citing_data = {}
            for cite_doi in citing_dois:
                if cite_doi in citing_results and citing_results[cite_doi].get('status') == 'success':
                    citing_data[cite_doi] = citing_results[cite_doi]
            
            # Анализ
            analysis = self._perform_medium_insight_analysis(doi, result, citing_data, journal_stats)
            medium_insights.append(analysis)
            
            # Кэшируем результаты
            self.cache.set_ethical_analysis('medium_insights', doi, analysis)
        
        return sorted(medium_insights, key=lambda x: x['Anomaly_Score'], reverse=True)
    
    def _collect_journal_statistics(self, analyzed_results: Dict[str, Dict], 
                                   citing_results: Dict[str, Dict]) -> Dict[str, Dict]:
        """Собирает статистику по журналам для нормализации"""
        journal_data = defaultdict(list)
        
        # Собираем данные по всем статьям
        all_results = list(analyzed_results.values()) + list(citing_results.values())
        
        for result in all_results:
            if result.get('status') != 'success':
                continue
            
            pub_info = result.get('publication_info', {})
            journal = pub_info.get('journal', '')
            citation_count = pub_info.get('citation_count_crossref', 0)
            year_str = pub_info.get('year', '')
            
            if journal and year_str:
                try:
                    year = int(year_str)
                    current_year = datetime.now().year
                    age = max(1, current_year - year)
                    annual_citations = citation_count / age
                    
                    journal_data[journal].append({
                        'annual_citations': annual_citations,
                        'citation_count': citation_count,
                        'year': year
                    })
                except:
                    continue
        
        # Рассчитываем медианы и квартили
        journal_stats = {}
        for journal, data_list in journal_data.items():
            if len(data_list) >= 3:  # Нужно минимум 3 статьи для статистики
                annual_citations = [d['annual_citations'] for d in data_list]
                annual_citations.sort()
                
                median_index = len(annual_citations) // 2
                q1_index = len(annual_citations) // 4
                q3_index = 3 * len(annual_citations) // 4

                journal_stats[journal] = {
                    'median_annual_citations': annual_citations[median_index],
                    'q1_annual_citations': annual_citations[q1_index],
                    'q3_annual_citations': annual_citations[q3_index],
                    'count': len(data_list),
                    'min': min(annual_citations),
                    'max': max(annual_citations),
                    # Добавляем 'median' для совместимости со старым кодом
                    'median': annual_citations[median_index]
                }
        
        return journal_stats
    
    def _perform_medium_insight_analysis(self, doi: str, result: Dict, 
                                        citing_data: Dict[str, Dict], 
                                        journal_stats: Dict[str, Dict]) -> Dict:
        """Выполняет средний анализ для одной статьи"""
        
        pub_info = result['publication_info']
        authors = result.get('authors', [])
        countries = result.get('countries', [])
        
        # 1. Temporal Citation Pattern
        temporal_pattern = self._analyze_temporal_pattern(result, citing_data)
        
        # 2. Journal Concentration Analysis
        journal_concentration = self._analyze_journal_concentration(citing_data)
        
        # 3. Author Network Analysis
        author_network = self._analyze_author_network(authors, citing_data)
        
        # 4. Geographic Bias Analysis
        geographic_bias = self._analyze_geographic_bias(countries, citing_data)
        
        # 5. Comparison with Journal Norms
        journal_comparison = self._compare_with_journal_norms(pub_info, journal_stats)
        
        # Расчет аномального скора
        anomaly_score = self._calculate_anomaly_score(
            temporal_pattern, journal_concentration, author_network,
            geographic_bias, journal_comparison
        )
        
        # Определение категории риска
        risk_category, investigation_priority = self._determine_risk_category(anomaly_score)
        
        return {
            'Article_DOI': doi,
            'Publication_Year': pub_info.get('year', ''),
            'Total_Citations': len(citing_data),
            'Annual_Citation_Rate': round(temporal_pattern.get('annual_rate', 0), 2),
            'Citations_Year_1': temporal_pattern.get('year_1', 0),
            'Citations_Year_2': temporal_pattern.get('year_2', 0),
            'First_2_Years_Percent': round(temporal_pattern.get('first_2_years_percent', 0) * 100, 1),
            'Temporal_Anomaly_Index': round(temporal_pattern.get('anomaly_index', 0), 3),
            'Top_Journal_Citing': journal_concentration.get('top_journal', ''),
            'Top_Journal_Percent': round(journal_concentration.get('top_journal_percent', 0) * 100, 1),
            'Journal_Concentration_Index': round(journal_concentration.get('concentration_index', 0), 3),
            'Journal_Diversity_Index': round(journal_concentration.get('diversity_index', 0), 3),
            'Author_Self_Citation_Rate': round(author_network.get('self_citation_rate', 0) * 100, 1),
            'Author_Cluster_Coefficient': round(author_network.get('cluster_coefficient', 0), 3),
            'Author_Network_Density': round(author_network.get('network_density', 0), 3),
            'Top_Country': geographic_bias.get('top_country', ''),
            'Top_Country_Percent': round(geographic_bias.get('top_country_percent', 0) * 100, 1),
            'Country_Diversity_Index': round(geographic_bias.get('diversity_index', 0), 3),
            'Geographic_Bias_Index': round(geographic_bias.get('bias_index', 0), 3),
            'Journal_Median_Annual_Cite': round(journal_comparison.get('journal_median', 0), 2),
            'Citation_Ratio_vs_Journal': round(journal_comparison.get('citation_ratio', 0), 2),
            'Journal_Percentile': round(journal_comparison.get('percentile', 0), 1),
            'Anomaly_Score': round(anomaly_score, 1),
            'Risk_Category': risk_category,
            'Investigation_Priority': investigation_priority,
            'Temporal_Red_Flags': temporal_pattern.get('red_flags', 0),
            'Journal_Red_Flags': journal_concentration.get('red_flags', 0),
            'Author_Red_Flags': author_network.get('red_flags', 0),
            'Geographic_Red_Flags': geographic_bias.get('red_flags', 0)
        }
    
    def _analyze_temporal_pattern(self, result: Dict, citing_data: Dict[str, Dict]) -> Dict:
        """Анализирует временные паттерны цитирования"""
        if not citing_data:
            return {'annual_rate': 0, 'year_1': 0, 'year_2': 0, 
                    'first_2_years_percent': 0, 'anomaly_index': 0, 'red_flags': 0}
        
        pub_year_str = result.get('publication_info', {}).get('year', '')
        if not pub_year_str:
            return {'annual_rate': 0, 'year_1': 0, 'year_2': 0, 
                    'first_2_years_percent': 0, 'anomaly_index': 0, 'red_flags': 0}
        
        try:
            pub_year = int(pub_year_str)
            current_year = datetime.now().year
            years_passed = max(1, current_year - pub_year)
            
            # Распределение по годам
            year_distribution = Counter()
            for cite_result in citing_data.values():
                cite_year_str = cite_result.get('publication_info', {}).get('year', '')
                if cite_year_str:
                    try:
                        cite_year = int(cite_year_str)
                        if cite_year >= pub_year:
                            year_distribution[cite_year] += 1
                    except:
                        pass
            
            # Основные метрики
            total_citations = len(citing_data)
            annual_rate = total_citations / years_passed
            
            year_1 = year_distribution.get(pub_year, 0)
            year_2 = year_distribution.get(pub_year + 1, 0)
            
            first_2_years = year_1 + year_2
            first_2_years_percent = first_2_years / total_citations if total_citations > 0 else 0
            
            # Индекс аномалии (чем выше, тем более аномальное распределение)
            expected_per_year = total_citations / max(1, len(year_distribution))
            anomaly_sum = 0
            for year, count in year_distribution.items():
                if expected_per_year > 0:
                    anomaly_sum += abs(count - expected_per_year) / expected_per_year
            
            anomaly_index = anomaly_sum / len(year_distribution) if year_distribution else 0
            
            # Красные флаги
            red_flags = 0
            if first_2_years_percent > Config.MEDIUM_INSIGHT_THRESHOLDS['first_two_years']:
                red_flags += 1
            if anomaly_index > 0.5:  # Сильное отклонение от равномерного распределения
                red_flags += 1
            
            return {
                'annual_rate': annual_rate,
                'year_1': year_1,
                'year_2': year_2,
                'first_2_years_percent': first_2_years_percent,
                'anomaly_index': anomaly_index,
                'red_flags': red_flags
            }
            
        except Exception as e:
            st.warning(f"⚠️ Temporal pattern analysis error: {e}")
            return {'annual_rate': 0, 'year_1': 0, 'year_2': 0, 
                    'first_2_years_percent': 0, 'anomaly_index': 0, 'red_flags': 0}
    
    def _analyze_journal_concentration(self, citing_data: Dict[str, Dict]) -> Dict:
        """Анализирует концентрацию цитирований по журналам"""
        if not citing_data:
            return {'top_journal': '', 'top_journal_percent': 0, 
                    'concentration_index': 0, 'diversity_index': 0, 'red_flags': 0}
        
        journal_counter = Counter()
        for cite_result in citing_data.values():
            journal = cite_result.get('publication_info', {}).get('journal', '')
            if journal:
                journal_counter[journal] += 1
        
        if not journal_counter:
            return {'top_journal': '', 'top_journal_percent': 0, 
                    'concentration_index': 0, 'diversity_index': 0, 'red_flags': 0}
        
        total_citations = sum(journal_counter.values())
        
        # Топ журнал и его доля
        top_journal, top_count = journal_counter.most_common(1)[0]
        top_journal_percent = top_count / total_citations
        
        # Индекс концентрации Херфиндаля-Хиршмана
        hhi = sum((count / total_citations) ** 2 for count in journal_counter.values())
        concentration_index = hhi
        
        # Индекс разнообразия (1 - HHI)
        diversity_index = 1 - hhi
        
        # Красные флаги
        red_flags = 0
        if top_journal_percent > Config.MEDIUM_INSIGHT_THRESHOLDS['top_journal_share']:
            red_flags += 1
        if concentration_index > 0.25:  # Высокая концентрация
            red_flags += 1
        
        return {
            'top_journal': top_journal[:50],
            'top_journal_percent': top_journal_percent,
            'concentration_index': concentration_index,
            'diversity_index': diversity_index,
            'red_flags': red_flags
        }
    
    def _analyze_author_network(self, analyzed_authors: List[Dict], 
                               citing_data: Dict[str, Dict]) -> Dict:
        """Анализирует сеть авторов цитирований"""
        if not citing_data or not analyzed_authors:
            return {'self_citation_rate': 0, 'cluster_coefficient': 0, 
                    'network_density': 0, 'red_flags': 0}
        
        analyzed_author_names = {author['name'] for author in analyzed_authors}
        
        # Строим сеть авторов цитирующих статей
        author_network = defaultdict(set)
        all_citing_authors = set()
        
        for cite_result in citing_data.values():
            citing_authors = cite_result.get('authors', [])
            citing_author_names = {author['name'] for author in citing_authors}
            all_citing_authors.update(citing_author_names)
            
            # Добавляем связи между всеми авторами одной статьи
            author_list = list(citing_author_names)
            for i in range(len(author_list)):
                for j in range(i + 1, len(author_list)):
                    author_network[author_list[i]].add(author_list[j])
                    author_network[author_list[j]].add(author_list[i])
        
        # Self-citation rate
        total_citations = len(citing_data)
        self_citations = 0
        
        for cite_result in citing_data.values():
            citing_authors = cite_result.get('authors', [])
            citing_author_names = {author['name'] for author in citing_authors}
            
            if analyzed_author_names.intersection(citing_author_names):
                self_citations += 1
        
        self_citation_rate = self_citations / total_citations if total_citations > 0 else 0
        
        # Коэффициент кластеризации (упрощенный)
        if len(author_network) > 0:
            total_possible_connections = len(author_network) * (len(author_network) - 1) / 2
            actual_connections = sum(len(neighbors) for neighbors in author_network.values()) / 2
            
            if total_possible_connections > 0:
                network_density = actual_connections / total_possible_connections
                
                # Упрощенный коэффициент кластеризации
                cluster_coefficient = network_density
            else:
                network_density = 0
                cluster_coefficient = 0
        else:
            network_density = 0
            cluster_coefficient = 0
        
        # Красные флаги
        red_flags = 0
        if self_citation_rate > 0.3:
            red_flags += 1
        if cluster_coefficient > Config.MEDIUM_INSIGHT_THRESHOLDS['cluster_coefficient']:
            red_flags += 1
        
        return {
            'self_citation_rate': self_citation_rate,
            'cluster_coefficient': cluster_coefficient,
            'network_density': network_density,
            'red_flags': red_flags
        }
    
    def _analyze_geographic_bias(self, analyzed_countries: List[str], 
                                citing_data: Dict[str, Dict]) -> Dict:
        """Анализирует географическую предвзятость"""
        if not citing_data:
            return {'top_country': '', 'top_country_percent': 0, 
                    'diversity_index': 0, 'bias_index': 0, 'red_flags': 0}
        
        country_counter = Counter()
        for cite_result in citing_data.values():
            countries = cite_result.get('countries', [])
            for country in countries:
                if country:
                    country_counter[country] += 1
        
        if not country_counter:
            return {'top_country': '', 'top_country_percent': 0, 
                    'diversity_index': 0, 'bias_index': 0, 'red_flags': 0}
        
        total_citations = sum(country_counter.values())
        
        # Топ страна и ее доля
        top_country, top_count = country_counter.most_common(1)[0]
        top_country_percent = top_count / total_citations
        
        # Индекс разнообразия
        hhi = sum((count / total_citations) ** 2 for count in country_counter.values())
        diversity_index = 1 - hhi
        
        # Индекс географической предвзятости
        # (доля из той же страны, что и анализируемая статья)
        same_country_share = 0
        if analyzed_countries:
            for country in analyzed_countries:
                same_country_share += country_counter.get(country, 0) / total_citations
        
        bias_index = same_country_share
        
        # Красные флаги
        red_flags = 0
        if top_country_percent > 0.8:
            red_flags += 1
        if bias_index > Config.MEDIUM_INSIGHT_THRESHOLDS['geographic_bias']:
            red_flags += 1
        
        return {
            'top_country': top_country,
            'top_country_percent': top_country_percent,
            'diversity_index': diversity_index,
            'bias_index': bias_index,
            'red_flags': red_flags
        }
    
    def _compare_with_journal_norms(self, pub_info: Dict, 
                                   journal_stats: Dict[str, Dict]) -> Dict:
        """Сравнивает с нормами журнала"""
        journal = pub_info.get('journal', '')
        citation_count = pub_info.get('citation_count_crossref', 0)
        year_str = pub_info.get('year', '')
        
        if not journal or not year_str or journal not in journal_stats:
            return {'journal_median': 0, 'citation_ratio': 0, 'percentile': 50}
        
        try:
            year = int(year_str)
            current_year = datetime.now().year
            age = max(1, current_year - year)
            annual_citations = citation_count / age
            
            stats = journal_stats[journal]
            journal_median = stats.get('median_annual_citations', 0.1)
            
            if journal_median > 0:
                citation_ratio = annual_citations / journal_median
            else:
                citation_ratio = 0
            
            # Процентиль относительно журнальных норм
            all_citations = [annual_citations]
            # Добавляем статистические значения из журнальных норм
            all_citations.append(stats.get('min', annual_citations * 0.5))
            all_citations.append(stats.get('median_annual_citations', annual_citations))
            all_citations.append(stats.get('max', annual_citations * 2))
            all_citations.sort()
            
            position = all_citations.index(annual_citations) + 1
            percentile = (position / len(all_citations)) * 100
            
            return {
                'journal_median': journal_median,
                'citation_ratio': citation_ratio,
                'percentile': percentile
            }
            
        except Exception as e:
            st.warning(f"⚠️ Journal comparison error: {e}")
            return {'journal_median': 0, 'citation_ratio': 0, 'percentile': 50}
    
    def _calculate_anomaly_score(self, temporal_pattern: Dict, journal_concentration: Dict,
                                author_network: Dict, geographic_bias: Dict, 
                                journal_comparison: Dict) -> float:
        """Рассчитывает общий аномальный скор"""
        score = 0
        
        # Временные аномалии (макс 25)
        score += min(25, temporal_pattern.get('anomaly_index', 0) * 50)
        if temporal_pattern.get('first_2_years_percent', 0) > 0.7:
            score += 15
        
        # Концентрация журналов (макс 20)
        score += min(20, journal_concentration.get('concentration_index', 0) * 80)
        if journal_concentration.get('top_journal_percent', 0) > 0.6:
            score += 10
        
        # Сеть авторов (макс 25)
        score += min(25, author_network.get('self_citation_rate', 0) * 83)
        score += min(15, author_network.get('cluster_coefficient', 0) * 20)
        
        # Географическая предвзятость (макс 15)
        score += min(15, geographic_bias.get('bias_index', 0) * 30)
        if geographic_bias.get('top_country_percent', 0) > 0.8:
            score += 5
        
        # Отклонение от журнальных норм (макс 15)
        citation_ratio = journal_comparison.get('citation_ratio', 0)
        if citation_ratio > 3:
            score += 15
        elif citation_ratio > 2:
            score += 10
        elif citation_ratio > 1.5:
            score += 5
        
        return min(100, score)
    
    def _determine_risk_category(self, anomaly_score: float) -> Tuple[str, int]:
        """Определяет категорию риска и приоритет расследования"""
        if anomaly_score > 80:
            return "CRITICAL", 5
        elif anomaly_score > 60:
            return "HIGH", 4
        elif anomaly_score > 40:
            return "MEDIUM", 3
        elif anomaly_score > 20:
            return "LOW", 2
        else:
            return "MINIMAL", 1
    
    def analyze_deep_analysis(self, analyzed_results: Dict[str, Dict], 
                             citing_results: Dict[str, Dict],
                             ref_results: Dict[str, Dict] = None) -> List[Dict]:
        """Глубокий анализ (60-120 секунд на статью)"""
        deep_analysis = []
        
        # Строим полную сеть для сетевого анализа
        full_network = self._build_citation_network(analyzed_results, citing_results, ref_results)
        
        for doi, result in analyzed_results.items():
            if result.get('status') != 'success':
                continue
            
            # Получаем связанные данные
            citing_dois = result.get('citations', [])
            citing_data = {}
            for cite_doi in citing_dois:
                if cite_doi in citing_results and citing_results[cite_doi].get('status') == 'success':
                    citing_data[cite_doi] = citing_results[cite_doi]
            
            # Выполняем глубокий анализ
            analysis = self._perform_deep_analysis(doi, result, citing_data, full_network)
            deep_analysis.append(analysis)
            
            # Кэшируем результаты
            self.cache.set_ethical_analysis('deep_analysis', doi, analysis)
        
        return sorted(deep_analysis, key=lambda x: x['Machine_Learning_Risk_Score'], reverse=True)
    
    def _build_citation_network(self, analyzed_results: Dict[str, Dict], 
                               citing_results: Dict[str, Dict],
                               ref_results: Dict[str, Dict] = None) -> nx.DiGraph:
        """Строит направленный граф цитирований"""
        G = nx.DiGraph()
        
        # Добавляем анализируемые статьи
        for doi, result in analyzed_results.items():
            if result.get('status') == 'success':
                G.add_node(doi, type='analyzed', 
                          year=result.get('publication_info', {}).get('year', ''))
        
        # Добавляем цитирующие статьи
        for doi, result in citing_results.items():
            if result.get('status') == 'success':
                G.add_node(doi, type='citing',
                          year=result.get('publication_info', {}).get('year', ''))
        
        # Добавляем референсы если есть
        if ref_results:
            for doi, result in ref_results.items():
                if result.get('status') == 'success':
                    G.add_node(doi, type='reference',
                              year=result.get('publication_info', {}).get('year', ''))
        
        # Добавляем ребра цитирований
        for analyzed_doi, result in analyzed_results.items():
            if result.get('status') == 'success':
                citing_dois = result.get('citations', [])
                for cite_doi in citing_dois:
                    if cite_doi in G:
                        G.add_edge(cite_doi, analyzed_doi)  # cite_doi → analyzed_doi
        
        return G
    
    def _perform_deep_analysis(self, doi: str, result: Dict, 
                              citing_data: Dict[str, Dict], 
                              citation_network: nx.DiGraph) -> Dict:
        """Выполняет глубокий анализ для одной статьи"""
        
        # 1. Network Analysis
        network_metrics = self._analyze_network_metrics(doi, citation_network)
        
        # 2. Temporal Pattern Mining
        temporal_patterns = self._mine_temporal_patterns(result, citing_data)
        
        # 3. Geographic Cluster Analysis
        geographic_clusters = self._analyze_geographic_clusters(result, citing_data)
        
        # 4. Journal Network Analysis
        journal_network = self._analyze_journal_network(result, citing_data)
        
        # 5. Statistical Anomaly Detection
        statistical_anomalies = self._detect_statistical_anomalies(result, citing_data)
        
        # 6. Machine Learning Risk Assessment
        ml_risk_score = self._calculate_ml_risk_score(
            network_metrics, temporal_patterns, geographic_clusters,
            journal_network, statistical_anomalies
        )
        
        # Определяем необходимость экспертного обзора
        expert_review_required = self._determine_expert_review_requirement(
            network_metrics, ml_risk_score, len(citing_data)
        )
        
        return {
            'Article_DOI': doi,
            'Author_Cluster_ID': network_metrics.get('author_cluster_id', 'N/A'),
            'Cluster_Size': network_metrics.get('cluster_size', 0),
            'Internal_Citation_Density': round(network_metrics.get('internal_density', 0), 3),
            'Cross_Cluster_Citations': network_metrics.get('cross_cluster_citations', 0),
            'Betweenness_Centrality': round(network_metrics.get('betweenness_centrality', 0), 4),
            'Clustering_Coefficient': round(network_metrics.get('clustering_coefficient', 0), 3),
            'Eigenvector_Centrality': round(network_metrics.get('eigenvector_centrality', 0), 4),
            'Quarterly_Citation_Peaks': temporal_patterns.get('quarterly_peaks', 0),
            'Seasonal_Pattern_Detected': temporal_patterns.get('seasonal_pattern', False),
            'Citation_Wave_Length': temporal_patterns.get('wave_length', 0),
            'Burst_Detection_Score': round(temporal_patterns.get('burst_score', 0), 3),
            'Geographic_Cluster_Strength': round(geographic_clusters.get('cluster_strength', 0), 3),
            'Cross_Country_Citation_Bias': round(geographic_clusters.get('cross_country_bias', 0), 3),
            'Region_Homophily_Index': round(geographic_clusters.get('homophily_index', 0), 3),
            'Journal_Citation_Circle': journal_network.get('citation_circle', False),
            'Journal_Reciprocity_Index': round(journal_network.get('reciprocity_index', 0), 3),
            'Predatory_Journal_Flags': journal_network.get('predatory_flags', 0),
            'Journal_Network_Modularity': round(journal_network.get('modularity', 0), 3),
            'Citation_Gini_Coefficient': round(statistical_anomalies.get('gini_coefficient', 0), 3),
            'Z_Score_Anomaly': round(statistical_anomalies.get('z_score', 0), 2),
            'Power_Law_Fit': round(statistical_anomalies.get('power_law_fit', 0), 3),
            'Statistical_Outlier_Flag': statistical_anomalies.get('outlier_flag', False),
            'Temporal_Anomaly_Score': round(temporal_patterns.get('temporal_anomaly_score', 0), 1),
            'Network_Centrality_Score': round(network_metrics.get('centrality_score', 0), 1),
            'Pattern_Anomaly_Score': round(temporal_patterns.get('pattern_anomaly_score', 0), 1),
            'Machine_Learning_Risk_Score': round(ml_risk_score, 1),
            'Expert_Review_Required': expert_review_required,
            'Suggested_Audit_Focus': self._suggest_audit_focus(network_metrics, temporal_patterns, 
                                                             geographic_clusters, journal_network),
            'Confidence_Level': self._calculate_confidence_level(len(citing_data), ml_risk_score)
        }
    
    def _analyze_network_metrics(self, doi: str, citation_network: nx.DiGraph) -> Dict:
        """Анализирует сетевые метрики"""
        if doi not in citation_network:
            return {'author_cluster_id': 'N/A', 'cluster_size': 0, 'internal_density': 0,
                    'cross_cluster_citations': 0, 'betweenness_centrality': 0,
                    'clustering_coefficient': 0, 'eigenvector_centrality': 0,
                    'centrality_score': 0}
        
        try:
            # Вычисляем центральности
            betweenness = nx.betweenness_centrality(citation_network, normalized=True).get(doi, 0)
            clustering = nx.clustering(citation_network.to_undirected()).get(doi, 0)
            
            # Eigenvector centrality (требует связного графа)
            try:
                eigenvector = nx.eigenvector_centrality_numpy(citation_network.to_undirected()).get(doi, 0)
            except:
                eigenvector = 0
            
            # Анализ сообществ (упрощенный)
            try:
                # Используем greedy modularity communities
                communities = list(nx.algorithms.community.greedy_modularity_communities(
                    citation_network.to_undirected()))
                
                # Находим сообщество текущей статьи
                article_community = None
                for i, community in enumerate(communities):
                    if doi in community:
                        article_community = i
                        break
                
                if article_community is not None:
                    community_nodes = communities[article_community]
                    cluster_size = len(community_nodes)
                    
                    # Плотность внутри сообщества
                    subgraph = citation_network.subgraph(community_nodes)
                    internal_edges = subgraph.number_of_edges()
                    possible_edges = len(community_nodes) * (len(community_nodes) - 1)
                    internal_density = internal_edges / possible_edges if possible_edges > 0 else 0
                    
                    # Цитирования между сообществами
                    cross_cluster_citations = 0
                    for node in community_nodes:
                        for neighbor in citation_network.neighbors(node):
                            if neighbor not in community_nodes:
                                cross_cluster_citations += 1
                    
                    author_cluster_id = f"COMM_{article_community:03d}"
                else:
                    cluster_size = 1
                    internal_density = 0
                    cross_cluster_citations = 0
                    author_cluster_id = "ISOLATED"
                    
            except:
                cluster_size = 1
                internal_density = 0
                cross_cluster_citations = 0
                author_cluster_id = "UNKNOWN"
            
            # Общий скоринг центральности
            centrality_score = min(100, (
                betweenness * 40 +
                eigenvector * 30 +
                (1 - clustering) * 30  # Низкий коэффициент кластеризации = выше центральность
            ))
            
            return {
                'author_cluster_id': author_cluster_id,
                'cluster_size': cluster_size,
                'internal_density': internal_density,
                'cross_cluster_citations': cross_cluster_citations,
                'betweenness_centrality': betweenness,
                'clustering_coefficient': clustering,
                'eigenvector_centrality': eigenvector,
                'centrality_score': centrality_score
            }
            
        except Exception as e:
            st.warning(f"⚠️ Network analysis error for {doi}: {e}")
            return {'author_cluster_id': 'N/A', 'cluster_size': 0, 'internal_density': 0,
                    'cross_cluster_citations': 0, 'betweenness_centrality': 0,
                    'clustering_coefficient': 0, 'eigenvector_centrality': 0,
                    'centrality_score': 0}
    
    def _mine_temporal_patterns(self, result: Dict, citing_data: Dict[str, Dict]) -> Dict:
        """Анализирует временные паттерны цитирования"""
        if not citing_data:
            return {'quarterly_peaks': 0, 'seasonal_pattern': False,
                    'wave_length': 0, 'burst_score': 0,
                    'temporal_anomaly_score': 0, 'pattern_anomaly_score': 0}
        
        pub_date_str = result.get('publication_info', {}).get('publication_date', '')
        if not pub_date_str:
            return {'quarterly_peaks': 0, 'seasonal_pattern': False,
                    'wave_length': 0, 'burst_score': 0,
                    'temporal_anomaly_score': 0, 'pattern_anomaly_score': 0}
        
        try:
            pub_date = datetime.strptime(pub_date_str[:10], '%Y-%m-%d')
            
            # Собираем даты цитирований
            citation_dates = []
            for cite_result in citing_data.values():
                cite_date_str = cite_result.get('publication_info', {}).get('publication_date', '')
                if cite_date_str:
                    try:
                        cite_date = datetime.strptime(cite_date_str[:10], '%Y-%m-%d')
                        if cite_date >= pub_date:  # Только будущие цитирования
                            citation_dates.append(cite_date)
                    except:
                        pass
            
            if not citation_dates:
                return {'quarterly_peaks': 0, 'seasonal_pattern': False,
                        'wave_length': 0, 'burst_score': 0,
                        'temporal_anomaly_score': 0, 'pattern_anomaly_score': 0}
            
            # Анализ по кварталам
            quarterly_counts = Counter()
            for date in citation_dates:
                quarter = f"{date.year}-Q{(date.month - 1) // 3 + 1}"
                quarterly_counts[quarter] += 1
            
            # Пики цитирований (кварталы с >30% от общего)
            total_citations = len(citation_dates)
            quarterly_peaks = 0
            for quarter, count in quarterly_counts.items():
                if count / total_citations > 0.3:
                    quarterly_peaks += 1
            
            # Сезонность (цитирования концентрируются в определенные месяцы)
            monthly_counts = Counter()
            for date in citation_dates:
                monthly_counts[date.month] += 1
            
            # Проверка на сезонность (более 40% в 2 месяца)
            sorted_months = sorted(monthly_counts.items(), key=lambda x: x[1], reverse=True)
            top_2_months_share = sum(count for _, count in sorted_months[:2]) / total_citations
            seasonal_pattern = top_2_months_share > 0.4
            
            # Длина "волны" цитирований (в днях)
            if len(citation_dates) >= 2:
                citation_dates.sort()
                time_spread = (citation_dates[-1] - citation_dates[0]).days
                
                # Нормализованная длина волны (0-1)
                if time_spread > 0:
                    wave_length = min(1.0, total_citations / (time_spread / 30.44))  # нормализация к месяцам
                else:
                    wave_length = 1.0
            else:
                wave_length = 0
            
            # Оценка "burst" активности
            if len(citation_dates) >= 3:
                # Среднее время между цитированиями
                citation_dates.sort()
                time_diffs = []
                for i in range(1, len(citation_dates)):
                    diff = (citation_dates[i] - citation_dates[i-1]).days
                    time_diffs.append(diff)
                
                if time_diffs:
                    avg_diff = sum(time_diffs) / len(time_diffs)
                    # Burst score: чем больше отклонение от среднего, тем выше
                    burst_variance = sum((d - avg_diff) ** 2 for d in time_diffs) / len(time_diffs)
                    burst_score = min(1.0, burst_variance / (avg_diff ** 2) if avg_diff > 0 else 0)
                else:
                    burst_score = 0
            else:
                burst_score = 0
            
            # Временной аномальный скор
            temporal_anomaly_score = min(100, (
                quarterly_peaks * 20 +
                (1 if seasonal_pattern else 0) * 30 +
                wave_length * 25 +
                burst_score * 25
            ))
            
            # Паттерн аномальный скор
            pattern_anomaly_score = min(100, (
                (quarterly_peaks / max(1, len(quarterly_counts))) * 40 +
                top_2_months_share * 30 +
                burst_score * 30
            ))
            
            return {
                'quarterly_peaks': quarterly_peaks,
                'seasonal_pattern': seasonal_pattern,
                'wave_length': round(wave_length, 3),
                'burst_score': round(burst_score, 3),
                'temporal_anomaly_score': temporal_anomaly_score,
                'pattern_anomaly_score': pattern_anomaly_score
            }
            
        except Exception as e:
            st.warning(f"⚠️ Temporal pattern mining error: {e}")
            return {'quarterly_peaks': 0, 'seasonal_pattern': False,
                    'wave_length': 0, 'burst_score': 0,
                    'temporal_anomaly_score': 0, 'pattern_anomaly_score': 0}
    
    def _analyze_geographic_clusters(self, result: Dict, citing_data: Dict[str, Dict]) -> Dict:
        """Анализирует географические кластеры"""
        if not citing_data:
            return {'cluster_strength': 0, 'cross_country_bias': 0,
                    'homophily_index': 0}
        
        analyzed_countries = set(result.get('countries', []))
        
        # Собираем страны цитирований
        citation_countries = []
        country_counter = Counter()
        
        for cite_result in citing_data.values():
            countries = cite_result.get('countries', [])
            citation_countries.append(set(countries))
            for country in countries:
                if country:
                    country_counter[country] += 1
        
        if not country_counter:
            return {'cluster_strength': 0, 'cross_country_bias': 0,
                    'homophily_index': 0}
        
        total_citations = len(citation_countries)
        
        # Сила географического кластера
        # (доля цитирований из наиболее частой страны)
        top_country_share = country_counter.most_common(1)[0][1] / total_citations
        cluster_strength = top_country_share
        
        # Межстрановой bias (доля цитирований из тех же стран)
        same_country_citations = 0
        for countries in citation_countries:
            if analyzed_countries.intersection(countries):
                same_country_citations += 1
        
        cross_country_bias = same_country_citations / total_citations if total_citations > 0 else 0
        
        # Индекс гомофилии (предпочтение своей группы)
        # Рассчитываем как доля внутригрупповых связей
        homophily_index = cross_country_bias
        
        return {
            'cluster_strength': round(cluster_strength, 3),
            'cross_country_bias': round(cross_country_bias, 3),
            'homophily_index': round(homophily_index, 3)
        }
    
    def _analyze_journal_network(self, result: Dict, citing_data: Dict[str, Dict]) -> Dict:
        """Анализирует сеть журналов"""
        if not citing_data:
            return {'citation_circle': False, 'reciprocity_index': 0,
                    'predatory_flags': 0, 'modularity': 0}
        
        analyzed_journal = result.get('publication_info', {}).get('journal', '')
        
        # Собираем журналы цитирований
        journal_counter = Counter()
        journal_pairs = set()
        
        for cite_result in citing_data.values():
            journal = cite_result.get('publication_info', {}).get('journal', '')
            if journal:
                journal_counter[journal] += 1
                
                # Запоминаем пару журналов
                if analyzed_journal and journal != analyzed_journal:
                    journal_pair = tuple(sorted([analyzed_journal, journal]))
                    journal_pairs.add(journal_pair)
        
        # Проверка на цитатные круги (упрощенная)
        # Если есть взаимное цитирование между небольшим набором журналов
        citation_circle = False
        if len(journal_counter) <= 3 and sum(journal_counter.values()) > 5:
            # Мало журналов, много цитирований
            citation_circle = True
        
        # Индекс взаимности (сколько журналов имеют обратные связи)
        # Упрощенный расчет
        total_journals = len(journal_counter)
        if total_journals > 0:
            # Предполагаем, что если журнал цитирует статью, 
            # то возможна обратная связь в других статьях
            reciprocity_index = min(1.0, total_journals / 10)
        else:
            reciprocity_index = 0
        
        # Флаги хищнических журналов (упрощенно по названию)
        predatory_keywords = ['international journal', 'advances in', 'research journal',
                            'journal of', 'annals of', 'archives of', 'european journal']
        
        predatory_flags = 0
        for journal in journal_counter:
            journal_lower = journal.lower()
            for keyword in predatory_keywords:
                if keyword in journal_lower:
                    predatory_flags += 1
                    break
        
        # Модулярность сети журналов (упрощенная)
        # Рассчитываем как 1 - (доля наиболее частого журнала)
        if journal_counter:
            top_journal_share = journal_counter.most_common(1)[0][1] / sum(journal_counter.values())
            modularity = 1 - top_journal_share
        else:
            modularity = 0
        
        return {
            'citation_circle': citation_circle,
            'reciprocity_index': round(reciprocity_index, 3),
            'predatory_flags': predatory_flags,
            'modularity': round(modularity, 3)
        }
    
    def _detect_statistical_anomalies(self, result: Dict, citing_data: Dict[str, Dict]) -> Dict:
        """Обнаруживает статистические аномалии"""
        if not citing_data:
            return {'gini_coefficient': 0, 'z_score': 0,
                    'power_law_fit': 0, 'outlier_flag': False}
        
        # Собираем годы цитирований для анализа распределения
        citation_years = []
        for cite_result in citing_data.values():
            year_str = cite_result.get('publication_info', {}).get('year', '')
            if year_str:
                try:
                    year = int(year_str)
                    citation_years.append(year)
                except:
                    pass
        
        if not citation_years:
            return {'gini_coefficient': 0, 'z_score': 0,
                    'power_law_fit': 0, 'outlier_flag': False}
        
        # Коэффициент Джини для неравномерности распределения
        citation_years.sort()
        n = len(citation_years)
        
        if n > 1:
            # Распределение по годам
            year_counts = Counter(citation_years)
            values = list(year_counts.values())
            values.sort()
            
            # Вычисляем коэффициент Джини
            cum_values = np.cumsum(values).astype(float)
            gini = (n + 1 - 2 * np.sum(cum_values) / cum_values[-1]) / n
        else:
            gini = 0
        
        # Z-score для выбросов в количестве цитирований
        pub_year_str = result.get('publication_info', {}).get('year', '')
        if pub_year_str and len(citation_years) >= 3:
            try:
                pub_year = int(pub_year_str)
                current_year = datetime.now().year
                
                # Среднее количество цитирований в год
                year_range = range(pub_year, current_year + 1)
                citations_per_year = []
                
                for year in year_range:
                    count = citation_years.count(year)
                    citations_per_year.append(count)
                
                mean_citations = np.mean(citations_per_year)
                std_citations = np.std(citations_per_year)
                
                if std_citations > 0:
                    # Z-score для года с максимальным количеством цитирований
                    max_year_count = max(citations_per_year)
                    z_score = (max_year_count - mean_citations) / std_citations
                else:
                    z_score = 0
            except:
                z_score = 0
        else:
            z_score = 0
        
        # Проверка на power-law распределение (упрощенная)
        # Если есть несколько лет с большим количеством цитирований
        if len(citation_years) >= 5:
            year_counts = Counter(citation_years)
            sorted_counts = sorted(year_counts.values(), reverse=True)
            
            # Проверяем, убывает ли экспоненциально
            if len(sorted_counts) >= 3:
                ratios = []
                for i in range(len(sorted_counts) - 1):
                    if sorted_counts[i+1] > 0:
                        ratios.append(sorted_counts[i] / sorted_counts[i+1])
                
                if ratios:
                    avg_ratio = np.mean(ratios)
                    # Чем выше среднее соотношение, тем ближе к power-law
                    power_law_fit = min(1.0, avg_ratio / 3)
                else:
                    power_law_fit = 0
            else:
                power_law_fit = 0
        else:
            power_law_fit = 0
        
        # Флаг выброса
        outlier_flag = (z_score > 3) or (gini > 0.7) or (power_law_fit > 0.8)
        
        return {
            'gini_coefficient': round(gini, 3),
            'z_score': round(z_score, 2),
            'power_law_fit': round(power_law_fit, 3),
            'outlier_flag': outlier_flag
        }
    
    def _calculate_ml_risk_score(self, network_metrics: Dict, temporal_patterns: Dict,
                                geographic_clusters: Dict, journal_network: Dict,
                                statistical_anomalies: Dict) -> float:
        """Рассчитывает ML-based риск скоринг"""
        score = 0
        
        # Сетевые метрики (макс 30)
        score += min(30, network_metrics.get('centrality_score', 0) * 0.3)
        
        # Временные паттерны (макс 25)
        score += min(25, temporal_patterns.get('temporal_anomaly_score', 0) * 0.25)
        
        # Географические кластеры (макс 20)
        cluster_strength = geographic_clusters.get('cluster_strength', 0)
        cross_country_bias = geographic_clusters.get('cross_country_bias', 0)
        score += min(20, (cluster_strength + cross_country_bias) * 10)
        
        # Сеть журналов (макс 15)
        if journal_network.get('citation_circle', False):
            score += 10
        score += min(5, journal_network.get('predatory_flags', 0) * 2.5)
        
        # Статистические аномалии (макс 10)
        if statistical_anomalies.get('outlier_flag', False):
            score += 10
        
        return min(100, score)
    
    def _determine_expert_review_requirement(self, network_metrics: Dict, 
                                           ml_risk_score: float, 
                                           citation_count: int) -> bool:
        """Определяет, требуется ли экспертное рассмотрение"""
        if ml_risk_score > 70:
            return True
        
        if citation_count > 50 and network_metrics.get('centrality_score', 0) > 60:
            return True
        
        if network_metrics.get('cluster_size', 0) > 20:
            return True
        
        return False
    
    def _suggest_audit_focus(self, network_metrics: Dict, temporal_patterns: Dict,
                           geographic_clusters: Dict, journal_network: Dict) -> str:
        """Предлагает фокус для аудита"""
        factors = []
        
        if network_metrics.get('centrality_score', 0) > 60:
            factors.append(('Network', network_metrics.get('centrality_score', 0)))
        
        if temporal_patterns.get('temporal_anomaly_score', 0) > 60:
            factors.append(('Temporal', temporal_patterns.get('temporal_anomaly_score', 0)))
        
        if geographic_clusters.get('cluster_strength', 0) > 0.7:
            factors.append(('Geographic', geographic_clusters.get('cluster_strength', 0) * 100))
        
        if journal_network.get('citation_circle', False):
            factors.append(('Journal', 100))
        
        if factors:
            # Сортируем по значению и берем топ
            factors.sort(key=lambda x: x[1], reverse=True)
            return factors[0][0]
        else:
            return 'Normal'
    
    def _calculate_confidence_level(self, citation_count: int, 
                                  ml_risk_score: float) -> int:
        """Рассчитывает уровень уверенности в оценке"""
        if citation_count == 0:
            return 50
        
        base_confidence = min(90, citation_count * 2)
        
        if ml_risk_score > 80:
            # Высокий риск = выше уверенность в обнаружении
            confidence = min(95, base_confidence + 10)
        elif ml_risk_score > 60:
            confidence = min(90, base_confidence + 5)
        elif ml_risk_score > 40:
            confidence = base_confidence
        elif ml_risk_score > 20:
            confidence = max(60, base_confidence - 10)
        else:
            confidence = max(50, base_confidence - 20)
        
        return confidence
    
    def analyze_citing_relationships(self, analyzed_results: Dict[str, Dict], 
                                   citing_results: Dict[str, Dict]) -> List[Dict]:
        """Анализирует связи анализируемые ↔ цитирующие (30-60 сек)"""
        relationships = []
        
        # Строим граф для сетевого анализа
        citation_graph = self._build_citation_network(analyzed_results, citing_results)
        
        for analyzed_doi, analyzed_result in analyzed_results.items():
            if analyzed_result.get('status') != 'success':
                continue
            
            citing_dois = analyzed_result.get('citations', [])
            
            for citing_doi in citing_dois:
                if citing_doi in citing_results and citing_results[citing_doi].get('status') == 'success':
                    citing_result = citing_results[citing_doi]
                    
                    # Анализ связи
                    analysis = self._perform_relationship_analysis(
                        analyzed_doi, analyzed_result, 
                        citing_doi, citing_result, 
                        citation_graph
                    )
                    
                    relationships.append(analysis)
        
        return sorted(relationships, key=lambda x: x['Gift_Citation_Probability'], reverse=True)
    
    def _perform_relationship_analysis(self, analyzed_doi: str, analyzed_result: Dict,
                                     citing_doi: str, citing_result: Dict,
                                     citation_graph: nx.DiGraph) -> Dict:
        """Анализирует связь между двумя статьями"""
        
        # 1. Временная разница
        time_diff = self._calculate_time_difference(analyzed_result, citing_result)
        
        # 2. Общие авторы
        common_authors = self._find_common_authors(analyzed_result, citing_result)
        
        # 3. Общие аффилиации
        common_affiliations = self._find_common_affiliations(analyzed_result, citing_result)
        
        # 4. Сетевые метрики
        network_metrics = self._calculate_relationship_network_metrics(
            analyzed_doi, citing_doi, citation_graph
        )
        
        # 5. Вероятность "подарочного" цитирования
        gift_probability = self._calculate_gift_citation_probability(
            time_diff, common_authors, common_affiliations, network_metrics
        )
        
        # 6. Роль в сети
        network_role = self._determine_network_role(analyzed_doi, citing_doi, citation_graph)
        
        # 7. Временная синхронизация
        time_sync = self._calculate_time_synchronization(analyzed_result, citing_result, citation_graph)
        
        # Определение уровня риска
        relationship_risk, action_required = self._determine_relationship_risk(gift_probability)
        
        return {
            'Analyzed_DOI': analyzed_doi,
            'Citing_DOI': citing_doi,
            'Time_Difference_Days': time_diff,
            'Same_Authors': len(common_authors),
            'Same_Affiliations': len(common_affiliations),
            'Common_Authors_List': '; '.join(common_authors),
            'Common_Affiliations_List': '; '.join(common_affiliations),
            'Connection_Strength': network_metrics.get('connection_strength', 0),
            'Reciprocity_Flag': network_metrics.get('reciprocity', False),
            'Temporal_Anomaly': self._determine_temporal_anomaly(time_diff),
            'Group_Citation_Cluster': network_metrics.get('cluster_id', 'N/A'),
            'Cluster_Size': network_metrics.get('cluster_size', 1),
            'Intra_Cluster_Density': round(network_metrics.get('intra_cluster_density', 0), 3),
            'Citation_Wave_Position': network_metrics.get('wave_position', 'Normal'),
            'Time_Sync_Score': round(time_sync, 3),
            'Batch_Citation_Flag': network_metrics.get('batch_citation', False),
            'Bridge_Role': network_role,
            'Betweenness_Centrality': round(network_metrics.get('betweenness', 0), 4),
            'Clustering_Coefficient': round(network_metrics.get('clustering', 0), 3),
            'Gift_Citation_Probability': round(gift_probability, 1),
            'Citation_Circle_Member': network_metrics.get('citation_circle', False),
            'Artificial_Boost_Flag': gift_probability > 70,
            'Journal_Pair_Frequency': network_metrics.get('journal_pair_freq', 1),
            'Country_Pair': self._create_country_pair(analyzed_result, citing_result),
            'Aff_Pair_Strength': len(common_affiliations),
            'Relationship_Risk': relationship_risk,
            'Action_Required': action_required,
            'Notes': self._generate_relationship_notes(
                common_authors, common_affiliations, time_diff, gift_probability
            )
        }
    
    def _calculate_time_difference(self, analyzed_result: Dict, citing_result: Dict) -> Optional[int]:
        """Вычисляет временную разницу в днях"""
        analyzed_date_str = analyzed_result.get('publication_info', {}).get('publication_date', '')
        citing_date_str = citing_result.get('publication_info', {}).get('publication_date', '')
        
        if not analyzed_date_str or not citing_date_str:
            return None
        
        try:
            analyzed_date = datetime.strptime(analyzed_date_str[:10], '%Y-%m-%d')
            citing_date = datetime.strptime(citing_date_str[:10], '%Y-%m-%d')
            
            return (citing_date - analyzed_date).days
        except:
            return None
    
    def _find_common_authors(self, analyzed_result: Dict, citing_result: Dict) -> Set[str]:
        """Находит общих авторов"""
        analyzed_authors = {author['name'] for author in analyzed_result.get('authors', [])}
        citing_authors = {author['name'] for author in citing_result.get('authors', [])}
        
        return analyzed_authors.intersection(citing_authors)
    
    def _find_common_affiliations(self, analyzed_result: Dict, citing_result: Dict) -> Set[str]:
        """Находит общие аффилиации"""
        analyzed_affiliations = set()
        for author in analyzed_result.get('authors', []):
            analyzed_affiliations.update(author.get('affiliation', []))
        
        citing_affiliations = set()
        for author in citing_result.get('authors', []):
            citing_affiliations.update(author.get('affiliation', []))
        
        return analyzed_affiliations.intersection(citing_affiliations)
    
    def _calculate_relationship_network_metrics(self, analyzed_doi: str, citing_doi: str,
                                              citation_graph: nx.DiGraph) -> Dict:
        """Вычисляет сетевые метрики для связи"""
        metrics = {
            'connection_strength': 1,
            'reciprocity': False,
            'cluster_id': 'N/A',
            'cluster_size': 1,
            'intra_cluster_density': 0,
            'wave_position': 'Normal',
            'batch_citation': False,
            'betweenness': 0,
            'clustering': 0,
            'citation_circle': False,
            'journal_pair_freq': 1
        }
        
        if analyzed_doi not in citation_graph or citing_doi not in citation_graph:
            return metrics
        
        try:
            # Проверка взаимности
            if citation_graph.has_edge(analyzed_doi, citing_doi):
                metrics['reciprocity'] = True
            
            # Сила связи (на основе центральностей)
            try:
                betweenness = nx.betweenness_centrality(citation_graph, normalized=True)
                metrics['betweenness'] = betweenness.get(analyzed_doi, 0) + betweenness.get(citing_doi, 0)
                
                # Нормализованная сила связи
                metrics['connection_strength'] = min(10, int(metrics['betweenness'] * 20 + 1))
            except:
                pass
            
            # Коэффициент кластеризации
            try:
                undirected_graph = citation_graph.to_undirected()
                clustering = nx.clustering(undirected_graph)
                metrics['clustering'] = (clustering.get(analyzed_doi, 0) + clustering.get(citing_doi, 0)) / 2
            except:
                pass
            
            # Анализ сообществ
            try:
                communities = list(nx.algorithms.community.greedy_modularity_communities(
                    citation_graph.to_undirected()))
                
                # Находим сообщество
                for i, community in enumerate(communities):
                    if analyzed_doi in community and citing_doi in community:
                        metrics['cluster_id'] = f"CLUSTER_{i:03d}"
                        metrics['cluster_size'] = len(community)
                        
                        # Плотность внутри сообщества
                        subgraph = citation_graph.subgraph(community)
                        possible_edges = len(community) * (len(community) - 1)
                        if possible_edges > 0:
                            metrics['intra_cluster_density'] = subgraph.number_of_edges() / possible_edges
                        
                        break
            except:
                pass
            
            # Проверка на batch citation
            # (много цитирований в короткий период)
            analyzed_neighbors = list(citation_graph.predecessors(analyzed_doi))
            if len(analyzed_neighbors) > 10:
                # Проверяем, есть ли группы цитирований с близкими датами
                metrics['batch_citation'] = True
            
            # Проверка на цитатные круги
            try:
                # Ищем короткие циклы
                for path in nx.all_simple_paths(citation_graph, citing_doi, analyzed_doi, cutoff=3):
                    if len(path) <= 3:
                        metrics['citation_circle'] = True
                        break
            except:
                pass
            
        except Exception as e:
            st.warning(f"⚠️ Network metrics error for {analyzed_doi}-{citing_doi}: {e}")
        
        return metrics
    
    def _calculate_gift_citation_probability(self, time_diff: Optional[int],
                                           common_authors: Set[str],
                                           common_affiliations: Set[str],
                                           network_metrics: Dict) -> float:
        """Рассчитывает вероятность "подарочного" цитирования"""
        probability = 0
        
        # Общие авторы (сильный сигнал)
        if common_authors:
            probability += min(50, len(common_authors) * 20)
        
        # Общие аффилиации (средний сигнал)
        if common_affiliations:
            probability += min(40, len(common_affiliations) * 15)
        
        # Временная близость (слабый сигнал)
        if time_diff is not None:
            if abs(time_diff) < 30:  # Меньше месяца
                probability += 20
            elif abs(time_diff) < 90:  # Меньше 3 месяцев
                probability += 10
        
        # Сетевые метрики
        if network_metrics.get('reciprocity', False):
            probability += 15
        
        if network_metrics.get('citation_circle', False):
            probability += 20
        
        if network_metrics.get('batch_citation', False):
            probability += 10
        
        # Нормализация
        return min(100, probability)
    
    def _determine_network_role(self, analyzed_doi: str, citing_doi: str,
                               citation_graph: nx.DiGraph) -> str:
        """Определяет роль в сети"""
        if analyzed_doi not in citation_graph or citing_doi not in citation_graph:
            return "Normal"
        
        try:
            # Степени вершин
            analyzed_in_degree = citation_graph.in_degree(analyzed_doi)
            analyzed_out_degree = citation_graph.out_degree(analyzed_doi)
            citing_in_degree = citation_graph.in_degree(citing_doi)
            citing_out_degree = citation_graph.out_degree(citing_doi)
            
            # Определяем роль на основе степеней
            if analyzed_in_degree > 10 or citing_in_degree > 10:
                return "Hub"
            elif analyzed_out_degree > 5 or citing_out_degree > 5:
                return "Connector"
            else:
                return "Normal"
                
        except:
            return "Normal"
    
    def _calculate_time_synchronization(self, analyzed_result: Dict, citing_result: Dict,
                                      citation_graph: nx.DiGraph) -> float:
        """Рассчитывает уровень временной синхронизации"""
        # Упрощенный расчет
        time_diff = self._calculate_time_difference(analyzed_result, citing_result)
        
        if time_diff is None:
            return 0.5
        
        # Нормализация
        if abs(time_diff) < 30:
            return 0.8  # Высокая синхронизация
        elif abs(time_diff) < 90:
            return 0.6  # Средняя синхронизация
        elif abs(time_diff) < 365:
            return 0.4  # Низкая синхронизация
        else:
            return 0.2  # Очень низкая синхронизация
    
    def _determine_temporal_anomaly(self, time_diff: Optional[int]) -> str:
        """Определяет временную аномалию"""
        if time_diff is None:
            return "Unknown"
        
        if time_diff < 0:
            return "Future citation"
        elif time_diff < 30:
            return "Rapid citation"
        elif time_diff < 90:
            return "Prompt citation"
        else:
            return "Normal"
    
    def _create_country_pair(self, analyzed_result: Dict, citing_result: Dict) -> str:
        """Создает строку пары стран"""
        analyzed_countries = analyzed_result.get('countries', [''])[:1]
        citing_countries = citing_result.get('countries', [''])[:1]
        
        analyzed_country = analyzed_countries[0] if analyzed_countries else 'Unknown'
        citing_country = citing_countries[0] if citing_countries else 'Unknown'
        
        return f"{analyzed_country}→{citing_country}"
    
    def _determine_relationship_risk(self, gift_probability: float) -> Tuple[str, str]:
        """Определяет уровень риска связи"""
        if gift_probability > 80:
            return "CRITICAL", "IMMEDIATE VALIDATION REQUIRED"
        elif gift_probability > 60:
            return "HIGH", "DETAILED REVIEW REQUIRED"
        elif gift_probability > 40:
            return "MEDIUM", "MONITOR AND REVIEW"
        elif gift_probability > 20:
            return "LOW", "MINOR REVIEW SUGGESTED"
        else:
            return "MINIMAL", "ETHICALLY ACCEPTABLE"
    
    def _generate_relationship_notes(self, common_authors: Set[str],
                                   common_affiliations: Set[str],
                                   time_diff: Optional[int],
                                   gift_probability: float) -> str:
        """Генерирует заметки о связи"""
        notes = []
        
        if common_authors:
            notes.append(f"Common authors: {len(common_authors)}")
        
        if common_affiliations:
            notes.append(f"Common affiliations: {len(common_affiliations)}")
        
        if time_diff is not None:
            if time_diff < 0:
                notes.append(f"Future citation: {abs(time_diff)} days before")
            else:
                notes.append(f"Time gap: {time_diff} days")
        
        notes.append(f"Gift citation probability: {gift_probability:.1f}%")
        
        return "; ".join(notes)

# ============================================================================
# 📊 КЛАСС ЭКСПОРТА В EXCEL (УЛУЧШЕННЫЙ С НОВЫМИ ФУНКЦИЯМИ)
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
        
        self.author_stats = defaultdict(lambda: {
            'normalized_name': '',
            'orcid': '',
            'affiliation': '',
            'country': '',
            'total_count': 0,
            'normalized_analyzed': 0,
            'normalized_reference': 0,
            'normalized_citing': 0
        })
        
        self.affiliation_stats = defaultdict(lambda: {
            'colab_id': '',
            'website': '',
            'countries': [],
            'total_count': 0,
            'normalized_analyzed': 0,
            'normalized_reference': 0,
            'normalized_citing': 0
        })
        
        self.affiliation_country_stats = defaultdict(lambda: defaultdict(int))
        self.current_year = datetime.now().year
        
        # Инициализация анализатора
        self.hierarchical_analyzer = None
    
    def set_hierarchical_analyzer(self, hierarchical_analyzer: HierarchicalDataAnalyzer):
        """Устанавливает анализатор для иерархического анализа"""
        self.hierarchical_analyzer = hierarchical_analyzer
    
    def _correct_country_for_author(self, author_key: str, affiliation_stats: Dict[str, Any]) -> str:
        """Correct country for author based on affiliation statistics"""
        author_info = self.author_stats[author_key]
        if not author_info['affiliation']:
            return author_info['country']
        
        affiliation = author_info['affiliation']
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
    
    def _analyze_ethical_insights(self, analysis_types: Dict[str, bool]) -> Dict[str, Any]:
        """Analyze ethical insights from collected data"""
        insights = {
            'quick_checks': [],
            'medium_insights': [],
            'deep_analysis': [],
            'analyzed_citing_relationships': []
        }
        
        if not self.hierarchical_analyzer:
            st.warning("⚠️ Hierarchical analyzer not set. Skipping ethical insights.")
            return insights
        
        # Выполняем только выбранные типы анализа
        if analysis_types.get('quick_checks', False):
            st.info("🔍 Performing Quick Checks analysis...")
            insights['quick_checks'] = self.hierarchical_analyzer.analyze_quick_checks(
                self.analyzed_results, self.citing_results
            )
        
        if analysis_types.get('medium_insights', False):
            st.info("🔍 Performing Medium Insights analysis...")
            insights['medium_insights'] = self.hierarchical_analyzer.analyze_medium_insights(
                self.analyzed_results, self.citing_results
            )
        
        if analysis_types.get('deep_analysis', False):
            st.info("🔍 Performing Deep Analysis...")
            insights['deep_analysis'] = self.hierarchical_analyzer.analyze_deep_analysis(
                self.analyzed_results, self.citing_results, self.ref_results
            )
        
        if analysis_types.get('analyzed_citing_relationships', False):
            st.info("🔍 Performing Analyzed-Citing Relationships analysis...")
            insights['analyzed_citing_relationships'] = self.hierarchical_analyzer.analyze_citing_relationships(
                self.analyzed_results, self.citing_results
            )
        
        return insights
    
    def create_comprehensive_report(self, analyzed_results: Dict[str, Dict], 
                                   ref_results: Dict[str, Dict] = None,
                                   citing_results: Dict[str, Dict] = None,
                                   analysis_types: Dict[str, bool] = None,
                                   filename: str = None) -> BytesIO:
        
        if filename is None:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = f"articles_analysis_comprehensive_{timestamp}.xlsx"
        
        st.info(f"📊 Creating comprehensive report: {filename}")
        
        # Устанавливаем типы анализа по умолчанию, если не указаны
        if analysis_types is None:
            analysis_types = {
                'quick_checks': True,
                'medium_insights': True,
                'deep_analysis': False,
                'analyzed_citing_relationships': False
            }
        
        self.analyzed_results = analyzed_results
        self.ref_results = ref_results or {}
        self.citing_results = citing_results or {}
        
        self._prepare_summary_data()
        
        # Generate ethical insights
        st.info("🔍 Generating ethical insights...")
        ethical_insights = self._analyze_ethical_insights(analysis_types)
        
        # Create Excel file in memory
        output = BytesIO()
        
        with pd.ExcelWriter(output, engine='openpyxl') as writer:
            st.info("📑 Generating sheets...")
            
            st.info("  1. Article_Analyzed...")
            analyzed_data = self._prepare_analyzed_articles(analyzed_results)
            if analyzed_data:
                df = pd.DataFrame(analyzed_data)
                df.to_excel(writer, sheet_name='Article_Analyzed', index=False)
            
            st.info("  2. Author freq_analyzed...")
            author_data = self._prepare_author_frequency(analyzed_results, "analyzed")
            if author_data:
                df = pd.DataFrame(author_data)
                df.to_excel(writer, sheet_name='Author freq_analyzed', index=False)
            
            st.info("  3. Journal freq_analyzed...")
            journal_data = self._prepare_journal_frequency(analyzed_results, "analyzed")
            if journal_data:
                df = pd.DataFrame(journal_data)
                df.to_excel(writer, sheet_name='Journal freq_analyzed', index=False)
            
            st.info("  4. Affiliation freq_analyzed...")
            affiliation_data = self._prepare_affiliation_frequency(analyzed_results, "analyzed")
            if affiliation_data:
                df = pd.DataFrame(affiliation_data)
                df.to_excel(writer, sheet_name='Affiliation freq_analyzed', index=False)
            
            st.info("  5. Country freq_analyzed...")
            country_data = self._prepare_country_frequency(analyzed_results, "analyzed")
            if country_data:
                df = pd.DataFrame(country_data)
                df.to_excel(writer, sheet_name='Country freq_analyzed', index=False)
            
            st.info("  6. Article_ref...")
            ref_data = self._prepare_article_ref()
            if ref_data:
                df = pd.DataFrame(ref_data)
                df.to_excel(writer, sheet_name='Article_ref', index=False)
            
            if ref_results:
                st.info("  7. Author freq_ref...")
                author_ref_data = self._prepare_author_frequency(ref_results, "ref")
                if author_ref_data:
                    df = pd.DataFrame(author_ref_data)
                    df.to_excel(writer, sheet_name='Author freq_ref', index=False)
                
                st.info("  8. Journal freq_ref...")
                journal_ref_data = self._prepare_journal_frequency(ref_results, "ref")
                if journal_ref_data:
                    df = pd.DataFrame(journal_ref_data)
                    df.to_excel(writer, sheet_name='Journal freq_ref', index=False)
                
                st.info("  9. Affiliation freq_ref...")
                affiliation_ref_data = self._prepare_affiliation_frequency(ref_results, "ref")
                if affiliation_ref_data:
                    df = pd.DataFrame(affiliation_ref_data)
                    df.to_excel(writer, sheet_name='Affiliation freq_ref', index=False)
                
                st.info("  10. Country freq_ref...")
                country_ref_data = self._prepare_country_frequency(ref_results, "ref")
                if country_ref_data:
                    df = pd.DataFrame(country_ref_data)
                    df.to_excel(writer, sheet_name='Country freq_ref', index=False)
            
            st.info("  11. Article_citing...")
            citing_data = self._prepare_article_citing()
            if citing_data:
                df = pd.DataFrame(citing_data)
                df.to_excel(writer, sheet_name='Article_citing', index=False)
            
            if citing_results:
                st.info("  12. Author freq_citing...")
                author_citing_data = self._prepare_author_frequency(citing_results, "citing")
                if author_citing_data:
                    df = pd.DataFrame(author_citing_data)
                    df.to_excel(writer, sheet_name='Author freq_citing', index=False)
                
                st.info("  13. Journal freq_citing...")
                journal_citing_data = self._prepare_journal_frequency(citing_results, "citing")
                if journal_citing_data:
                    df = pd.DataFrame(journal_citing_data)
                    df.to_excel(writer, sheet_name='Journal freq_citing', index=False)
                
                st.info("  14. Affiliation freq_citing...")
                affiliation_citing_data = self._prepare_affiliation_frequency(citing_results, "citing")
                if affiliation_citing_data:
                    df = pd.DataFrame(affiliation_citing_data)
                    df.to_excel(writer, sheet_name='Affiliation freq_citing', index=False)
                
                st.info("  15. Country freq_citing...")
                country_citing_data = self._prepare_country_frequency(citing_results, "citing")
                if country_citing_data:
                    df = pd.DataFrame(country_citing_data)
                    df.to_excel(writer, sheet_name='Country freq_citing', index=False)
            
            st.info("  16. Author_summary...")
            author_summary_data = self._prepare_author_summary()
            if author_summary_data:
                df = pd.DataFrame(author_summary_data)
                df.to_excel(writer, sheet_name='Author_summary', index=False)
            
            st.info("  17. Affiliation_summary...")
            affiliation_summary_data = self._prepare_affiliation_summary()
            if affiliation_summary_data:
                df = pd.DataFrame(affiliation_summary_data)
                df.to_excel(writer, sheet_name='Affiliation_summary', index=False)
            
            st.info("  18. Time (Ref,analyzed)_connections...")
            time_ref_analyzed_data = self._prepare_time_ref_analyzed_connections()
            if time_ref_analyzed_data:
                df = pd.DataFrame(time_ref_analyzed_data)
                df.to_excel(writer, sheet_name='Time (Ref,analyzed)_connections', index=False)
            
            st.info("  19. Time (analyzed,citing)_connections...")
            time_analyzed_citing_data = self._prepare_time_analyzed_citing_connections()
            if time_analyzed_citing_data:
                df = pd.DataFrame(time_analyzed_citing_data)
                df.to_excel(writer, sheet_name='Time (analyzed,citing)_connections', index=False)
            
            st.info("  20. Failed_DOI...")
            failed_data = self.failed_tracker.get_failed_for_excel()
            if failed_data:
                df = pd.DataFrame(failed_data)
                df.to_excel(writer, sheet_name='Failed_DOI', index=False)
            
            st.info("  21. Analysis_Stats...")
            stats_data = self._prepare_analysis_stats(analyzed_results, ref_results, citing_results)
            if stats_data:
                df = pd.DataFrame(stats_data)
                df.to_excel(writer, sheet_name='Analysis_Stats', index=False)
            
            # Ethical Insights Sheets (только если выбран соответствующий анализ)
            if analysis_types.get('quick_checks', False) and ethical_insights['quick_checks']:
                st.info("  22. Quick_Checks...")
                df = pd.DataFrame(ethical_insights['quick_checks'])
                df.to_excel(writer, sheet_name='Quick_Checks', index=False)
            
            if analysis_types.get('medium_insights', False) and ethical_insights['medium_insights']:
                st.info("  23. Medium_Insights...")
                df = pd.DataFrame(ethical_insights['medium_insights'])
                df.to_excel(writer, sheet_name='Medium_Insights', index=False)
            
            if analysis_types.get('deep_analysis', False) and ethical_insights['deep_analysis']:
                st.info("  24. Deep_Analysis...")
                df = pd.DataFrame(ethical_insights['deep_analysis'])
                df.to_excel(writer, sheet_name='Deep_Analysis', index=False)
            
            if analysis_types.get('analyzed_citing_relationships', False) and ethical_insights['analyzed_citing_relationships']:
                st.info("  25. Analyzed_Citing_Relationships...")
                df = pd.DataFrame(ethical_insights['analyzed_citing_relationships'])
                df.to_excel(writer, sheet_name='Analyzed_Citing_Relationships', index=False)
        
        output.seek(0)
        
        st.success(f"✅ Report created!")
        
        self._print_summary(analyzed_results, ref_results, citing_results, analysis_types)
        
        return output
    
    def _prepare_summary_data(self):
        st.info("   🔍 Preparing data for summary tables...")
        
        total_analyzed_articles = len([r for r in self.analyzed_results.values() if r.get('status') == 'success'])
        total_ref_articles = len([r for r in self.ref_results.values() if r.get('status') == 'success'])
        total_citing_articles = len([r for r in self.citing_results.values() if r.get('status') == 'success'])
        
        for doi, result in self.analyzed_results.items():
            if result.get('status') != 'success':
                continue
            
            self.source_dois['analyzed'].add(doi)
            
            for ref_doi in result.get('references', []):
                self.ref_to_analyzed[ref_doi].append(doi)
                self.doi_to_source_counts[ref_doi]['ref'] += 1
                self.source_dois['ref'].add(ref_doi)
            
            for cite_doi in result.get('citations', []):
                self.analyzed_to_citing[doi].append(cite_doi)
                self.doi_to_source_counts[cite_doi]['citing'] += 1
                self.source_dois['citing'].add(cite_doi)
            
            # Update author stats with normalized values
            for author in result.get('authors', []):
                full_name = author.get('name', '')
                if not full_name:
                    continue
                
                normalized_name = self.processor.normalize_author_name(full_name)
                key = normalized_name
                
                if author.get('orcid'):
                    key = f"{normalized_name}_{author['orcid']}"
                
                # Calculate normalized value for analyzed articles
                normalized_value = 1 / total_analyzed_articles if total_analyzed_articles > 0 else 0
                self.author_stats[key]['normalized_analyzed'] += normalized_value
                self.author_stats[key]['total_count'] += normalized_value
                
                if not self.author_stats[key]['orcid'] and author.get('orcid'):
                    self.author_stats[key]['orcid'] = self.processor._format_orcid_id(author.get('orcid', ''))
                
                if not self.author_stats[key]['affiliation'] and author.get('affiliation'):
                    self.author_stats[key]['affiliation'] = author.get('affiliation')[0] if author.get('affiliation') else ''
                
                if result.get('countries'):
                    country = result.get('countries')[0] if result.get('countries') else ''
                    if country and not self.author_stats[key]['country']:
                        self.author_stats[key]['country'] = country
                    
                    if self.author_stats[key]['affiliation']:
                        self.affiliation_country_stats[self.author_stats[key]['affiliation']][country] += 1
                
                self.author_stats[key]['normalized_name'] = normalized_name
            
            # Update affiliation stats with normalized values
            unique_affiliations_in_article = set()
            for author in result.get('authors', []):
                for affiliation in author.get('affiliation', []):
                    if affiliation:
                        unique_affiliations_in_article.add(affiliation)
            
            normalized_aff_value = 1 / total_analyzed_articles if total_analyzed_articles > 0 else 0
            for affiliation in unique_affiliations_in_article:
                self.affiliation_stats[affiliation]['normalized_analyzed'] += normalized_aff_value
                self.affiliation_stats[affiliation]['total_count'] += normalized_aff_value
                
                if result.get('countries'):
                    for country in result.get('countries'):
                        if country:
                            self.affiliation_stats[affiliation]['countries'].append(country)
        
        # Process ref results
        for doi, result in self.ref_results.items():
            if result.get('status') != 'success':
                continue
            
            # Update author stats for ref articles
            for author in result.get('authors', []):
                full_name = author.get('name', '')
                if not full_name:
                    continue
                
                normalized_name = self.processor.normalize_author_name(full_name)
                key = normalized_name
                
                if author.get('orcid'):
                    key = f"{normalized_name}_{author['orcid']}"
                
                # Calculate normalized value for ref articles
                normalized_value = 1 / total_ref_articles if total_ref_articles > 0 else 0
                self.author_stats[key]['normalized_reference'] += normalized_value
                self.author_stats[key]['total_count'] += normalized_value
                
                if not self.author_stats[key]['orcid'] and author.get('orcid'):
                    self.author_stats[key]['orcid'] = self.processor._format_orcid_id(author.get('orcid', ''))
                
                if not self.author_stats[key]['affiliation'] and author.get('affiliation'):
                    self.author_stats[key]['affiliation'] = author.get('affiliation')[0] if author.get('affiliation') else ''
                
                if not self.author_stats[key]['country'] and result.get('countries'):
                    self.author_stats[key]['country'] = result.get('countries')[0] if result.get('countries') else ''
                
                self.author_stats[key]['normalized_name'] = normalized_name
            
            # Update affiliation stats for ref articles
            unique_affiliations_in_article = set()
            for author in result.get('authors', []):
                for affiliation in author.get('affiliation', []):
                    if affiliation:
                        unique_affiliations_in_article.add(affiliation)
            
            normalized_aff_value = 1 / total_ref_articles if total_ref_articles > 0 else 0
            for affiliation in unique_affiliations_in_article:
                self.affiliation_stats[affiliation]['normalized_reference'] += normalized_aff_value
                self.affiliation_stats[affiliation]['total_count'] += normalized_aff_value
        
        # Process citing results
        for doi, result in self.citing_results.items():
            if result.get('status') != 'success':
                continue
            
            # Update author stats for citing articles
            for author in result.get('authors', []):
                full_name = author.get('name', '')
                if not full_name:
                    continue
                
                normalized_name = self.processor.normalize_author_name(full_name)
                key = normalized_name
                
                if author.get('orcid'):
                    key = f"{normalized_name}_{author['orcid']}"
                
                # Calculate normalized value for citing articles
                normalized_value = 1 / total_citing_articles if total_citing_articles > 0 else 0
                self.author_stats[key]['normalized_citing'] += normalized_value
                self.author_stats[key]['total_count'] += normalized_value
                
                if not self.author_stats[key]['orcid'] and author.get('orcid'):
                    self.author_stats[key]['orcid'] = self.processor._format_orcid_id(author.get('orcid', ''))
                
                if not self.author_stats[key]['affiliation'] and author.get('affiliation'):
                    self.author_stats[key]['affiliation'] = author.get('affiliation')[0] if author.get('affiliation') else ''
                
                if not self.author_stats[key]['country'] and result.get('countries'):
                    self.author_stats[key]['country'] = result.get('countries')[0] if result.get('countries') else ''
                
                self.author_stats[key]['normalized_name'] = normalized_name
            
            # Update affiliation stats for citing articles
            unique_affiliations_in_article = set()
            for author in result.get('authors', []):
                for affiliation in author.get('affiliation', []):
                    if affiliation:
                        unique_affiliations_in_article.add(affiliation)
            
            normalized_aff_value = 1 / total_citing_articles if total_citing_articles > 0 else 0
            for affiliation in unique_affiliations_in_article:
                self.affiliation_stats[affiliation]['normalized_citing'] += normalized_aff_value
                self.affiliation_stats[affiliation]['total_count'] += normalized_aff_value
        
        st.info("   🔍 Getting ROR data for affiliation summary...")
        affiliations_list = list(self.affiliation_stats.keys())
        
        progress_bar = st.progress(0)
        status_text = st.empty()
        
        for i, aff in enumerate(affiliations_list):
            ror_info = self.ror_client.search_organization(aff, category="summary")
            if ror_info.get('ror_id'):
                self.affiliation_stats[aff]['colab_id'] = ror_info.get('ror_id', '')
                self.affiliation_stats[aff]['website'] = ror_info.get('website', '')
            
            progress_bar.progress((i + 1) / len(affiliations_list))
            status_text.text(f"Processing {i+1}/{len(affiliations_list)} affiliations...")
        
        progress_bar.empty()
        status_text.empty()
    
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
                'references_count': len(ref_result.get('references', [])),
                'count': count
            }
            
            data.append(row)
        
        for ref_doi in self.ref_to_analyzed:
            if ref_doi not in processed_refs:
                count = len(self.ref_to_analyzed.get(ref_doi, []))
                row = {
                    'doi': ref_doi,
                    'publication_date': '',
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
                    'count': count
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
                'references_count': len(cite_result.get('references', [])),
                'count': count
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
                    'count': count
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
                'references_count': len(result.get('references', []))
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
                
                key = normalized_name
                if author.get('orcid'):
                    key = f"{normalized_name}_{author['orcid']}"
                
                author_counter[key] += 1
                
                if key not in author_details:
                    affiliation = author['affiliation'][0] if author.get('affiliation') else ""
                    orcid = author.get('orcid', '')
                    
                    author_details[key] = {
                        'orcid': self.processor._format_orcid_id(orcid) if orcid else '',
                        'affiliation': affiliation,
                        'country': result.get('countries', [''])[0] if result.get('countries') else '',
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
        
        for key, stats in self.author_stats.items():
            if stats['total_count'] == 0:
                continue
            
            # Calculate total count as sum of normalized values (as requested)
            total_count = stats['total_count']
            
            # Correct country
            corrected_country = self._correct_country_for_author(key, self.affiliation_stats)
            
            # Determine risk level based on normalized values
            risk_level = "NORMAL"
            risk_description = "Minimal author overlap between article types. Ethically acceptable."
            
            if stats['normalized_reference'] > 0.21:
                risk_level = "HIGH"
                risk_description = "Potential high self-citing for reference works"
            elif stats['normalized_citing'] > 0.5:
                risk_level = "HIGH"
                risk_description = "Potential high self-citing for citing works"
            elif total_count > 0.3:
                risk_level = "HIGH"
                risk_description = "HIGH RISK OF SELF-CITATION/CROWDING: author is present in analyzed articles and actively cites them or is cited in them. Thorough review recommended."
            elif total_count > 0.15:
                risk_level = "MEDIUM"
                risk_description = "MEDIUM LEVEL: moderate author presence in different article types. Possible normal academic interaction."
            elif total_count > 0.05:
                risk_level = "LOW"
                risk_description = "LOW LEVEL: small author presence in various article types. Likely normal academic practice."
            
            row = {
                'Surname + Initial_normalized': stats['normalized_name'],
                'ORCID ID': stats['orcid'],
                'Affiliation': stats['affiliation'],
                'Country': corrected_country,
                'Total Count': round(total_count, 4),
                'Normalized Analyzed': round(stats['normalized_analyzed'], 4),
                'Normalized Reference': round(stats['normalized_reference'], 4),
                'Normalized Citing': round(stats['normalized_citing'], 4),
                'Risk_Level': risk_level,
                'Risk_Description': risk_description
            }
            data.append(row)
        
        data.sort(key=lambda x: {'HIGH': 3, 'MEDIUM': 2, 'LOW': 1, 'NORMAL': 0}.get(x['Risk_Level'], 0), reverse=True)
        
        return data
    
    def _prepare_affiliation_summary(self) -> List[Dict]:
        data = []
        
        for affiliation, stats in self.affiliation_stats.items():
            if stats['total_count'] == 0:
                continue
            
            # Determine main country for affiliation
            main_country = ""
            if stats['countries']:
                country_counter = Counter(stats['countries'])
                main_country = country_counter.most_common(1)[0][0]
            
            row = {
                'Affiliation': affiliation,
                'Colab ID': stats['colab_id'],
                'Web Site': stats['website'],
                'Main Country': main_country,
                'total count': round(stats['total_count'], 4),
                'Normalized analyzed': round(stats['normalized_analyzed'], 4),
                'Normalized reference': round(stats['normalized_reference'], 4),
                'Normalized citing': round(stats['normalized_citing'], 4)
            }
            data.append(row)
        
        data.sort(key=lambda x: x['total count'], reverse=True)
        
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
        journal_counter = Counter()
        
        for doi, result in results.items():
            if result.get('status') != 'success':
                continue
            
            journal = result['publication_info'].get('journal', '')
            if journal:
                journal_counter[journal] += 1
        
        sorted_journals = sorted(journal_counter.items(), key=lambda x: x[1], reverse=True)
        
        return [{'Full Journal Name': journal, 'Count': count} 
                for journal, count in sorted_journals]
    
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
        
        st.info(f"   🔍 Collecting data for {len(unique_affiliations)} affiliations ({source_type})...")
        
        progress_bar = st.progress(0)
        status_text = st.empty()
        
        for i, aff in enumerate(unique_affiliations):
            row = {
                'Affiliation': aff,
                'Count': affiliation_counter[aff]
            }
            affiliation_data.append(row)
            
            progress_bar.progress((i + 1) / len(unique_affiliations))
            status_text.text(f"Processing {i+1}/{len(unique_affiliations)} affiliations...")
        
        progress_bar.empty()
        status_text.empty()
        
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
    
    def _print_summary(self, analyzed_results: Dict[str, Dict], 
                      ref_results: Dict[str, Dict], 
                      citing_results: Dict[str, Dict],
                      analysis_types: Dict[str, bool] = None):
        st.subheader("📊 ANALYSIS SUMMARY:")
        
        analyzed_success = sum(1 for r in analyzed_results.values() if r.get('status') == 'success')
        st.info(f"📚 Analyzed articles: {analyzed_success}/{len(analyzed_results)} successful")
        
        if analyzed_success > 0:
            total_authors = sum(len(r.get('authors', [])) for r in analyzed_results.values() if r.get('status') == 'success')
            total_refs = sum(len(r.get('references', [])) for r in analyzed_results.values() if r.get('status') == 'success')
            total_cites = sum(len(r.get('citations', [])) for r in analyzed_results.values() if r.get('status') == 'success')
            
            st.info(f"👥 Authors: {total_authors}")
            st.info(f"📎 References: {total_refs}")
            st.info(f"🔗 Citations: {total_cites}")
        
        if ref_results:
            ref_success = sum(1 for r in ref_results.values() if r.get('status') == 'success')
            st.info(f"📎 Reference articles: {ref_success}/{len(ref_results)} successful")
        
        if citing_results:
            cite_success = sum(1 for r in citing_results.values() if r.get('status') == 'success')
            st.info(f"🔗 Citation articles: {cite_success}/{len(citing_results)} successful")
        
        if analysis_types:
            st.subheader("🔍 Ethical Analysis Types:")
            for analysis_type, enabled in analysis_types.items():
                status = "✅ ENABLED" if enabled else "❌ DISABLED"
                st.info(f"• {analysis_type.replace('_', ' ').title()}: {status}")
        
        failed_stats = self.failed_tracker.get_stats()
        st.warning(f"❌ Failed DOI: {failed_stats['total_failed']}")
        st.warning(f"• From analyzed: {failed_stats['analyzed_failed']}")
        st.warning(f"• From references: {failed_stats['ref_failed']}")
        st.warning(f"• From citations: {failed_stats['citing_failed']}")
    
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
# 🎛️ КЛАСС УПРАВЛЕНИЯ ИНТЕРФЕЙСОМ STREAMLIT
# ============================================================================

class StreamlitInterfaceManager:
    def __init__(self, system):
        self.system = system
        self.initialize_session_state()
    
    def initialize_session_state(self):
        """Initialize Streamlit session state variables"""
        if 'system_initialized' not in st.session_state:
            st.session_state.system_initialized = False
        if 'processed_data' not in st.session_state:
            st.session_state.processed_data = None
        if 'excel_file' not in st.session_state:
            st.session_state.excel_file = None
        if 'analysis_types' not in st.session_state:
            st.session_state.analysis_types = {
                'quick_checks': True,
                'medium_insights': True,
                'deep_analysis': False,
                'analyzed_citing_relationships': False
            }
    
    def render_sidebar(self):
        """Render the sidebar controls"""
        with st.sidebar:
            st.header("⚙️ Настройки")
            
            # Workers setting
            st.subheader("Параллельность")
            workers = st.slider(
                "Количество потоков",
                min_value=Config.MIN_WORKERS,
                max_value=Config.MAX_WORKERS,
                value=Config.DEFAULT_WORKERS,
                help="Количество параллельных потоков для обработки DOI",
                key="workers_slider"  # Добавляем уникальный ключ
            )
            
            # Analysis types
            st.subheader("🔍 Типы анализа")
            st.session_state.analysis_types['quick_checks'] = st.checkbox(
                "Quick Checks (5-10 сек)", 
                value=st.session_state.analysis_types['quick_checks'],
                help="Быстрые проверки на неэтичные практики"
            )
            st.session_state.analysis_types['medium_insights'] = st.checkbox(
                "Medium Insights (15-30 сек)", 
                value=st.session_state.analysis_types['medium_insights'],
                help="Средние инсайты с детальным анализом"
            )
            st.session_state.analysis_types['deep_analysis'] = st.checkbox(
                "Deep Analysis (60-120 сек)", 
                value=st.session_state.analysis_types['deep_analysis'],
                help="Глубокий анализ с ML и сетевыми метриками"
            )
            st.session_state.analysis_types['analyzed_citing_relationships'] = st.checkbox(
                "Analyzed-Citing Relationships (30-60 сек)", 
                value=st.session_state.analysis_types['analyzed_citing_relationships'],
                help="Анализ связей между анализируемыми и цитирующими статьями"
            )
            
            # Cache controls
            st.subheader("🗂️ Управление кэшем")
            if st.button("🧹 Очистить кэш", type="secondary"):
                self.system.cache_manager.clear_all()
                st.success("Кэш очищен!")
            
            # Display cache stats
            cache_stats = self.system.cache_manager.get_stats()
            with st.expander("Статистика кэша"):
                st.metric("Эффективность", f"{cache_stats['hit_ratio']}%")
                st.metric("Сохранено API вызовов", cache_stats['api_calls_saved'])
                st.metric("Размер кэша", f"{cache_stats['cache_size_mb']} MB")
            
            return workers

            # Analysis types с ключами
            st.subheader("🔍 Типы анализа")
            st.session_state.analysis_types['quick_checks'] = st.checkbox(
                "Quick Checks (5-10 сек)", 
                value=st.session_state.analysis_types['quick_checks'],
                help="Быстрые проверки на неэтичные практики",
                key="quick_checks_checkbox"  # Добавляем ключ
            )
            st.session_state.analysis_types['medium_insights'] = st.checkbox(
                "Medium Insights (15-30 сек)", 
                value=st.session_state.analysis_types['medium_insights'],
                help="Средние инсайты с детальным анализом",
                key="medium_insights_checkbox"  # Добавляем ключ
            )
            st.session_state.analysis_types['deep_analysis'] = st.checkbox(
                "Deep Analysis (60-120 сек)", 
                value=st.session_state.analysis_types['deep_analysis'],
                help="Глубокий анализ с ML и сетевыми метриками",
                key="deep_analysis_checkbox"  # Добавляем ключ
            )
            st.session_state.analysis_types['analyzed_citing_relationships'] = st.checkbox(
                "Analyzed-Citing Relationships (30-60 сек)", 
                value=st.session_state.analysis_types['analyzed_citing_relationships'],
                help="Анализ связей между анализируемыми и цитирующими статьями",
                key="relationships_checkbox"  # Добавляем ключ
            )
    
    def render_main_interface(self):
        """Render the main interface"""
        st.title("📚 Анализатор научных статей по DOI")
        
        st.markdown("""
        ### Полный анализ научных статей с обнаружением неэтичных практик
        
        **Функционал:**
        - 📊 Умное кэширование всех уровней (память, файл, запросы)
        - 🔍 Иерархический анализ данных (4 уровня глубины)
        - ⚠️ Обнаружение неэтичных практик цитирования
        - 📈 25+ вкладок в Excel отчете
        - 🌐 Параллельная обработка до 10 потоков
        """)
        
        # DOI input
        st.subheader("📝 Введите DOI для анализа")
        doi_input = st.text_area(
            "Введите один или несколько DOI (через запятую, точку с запятой или новую строки)",
            height=150,
            placeholder="Примеры:\n10.1038/nature12373\n10.1126/science.1252914\n10.1016/j.cell.2019.11.017"
        )
        
        # Process button
        col1, col2, col3 = st.columns(3)
        with col1:
            process_btn = st.button("🚀 Обработать DOI", type="primary", use_container_width=True)
        with col2:
            clear_btn = st.button("🧹 Очистить", type="secondary", use_container_width=True)
        with col3:
            export_btn = st.button("💾 Экспорт Excel", type="secondary", use_container_width=True, 
                                 disabled=st.session_state.processed_data is None)
        
        if clear_btn:
            st.session_state.processed_data = None
            st.session_state.excel_file = None
            st.rerun()
        
        if process_btn and doi_input:
            self.process_dois(doi_input)
        
        if export_btn and st.session_state.processed_data:
            self.export_to_excel()
        
        # Display results if available
        if st.session_state.processed_data:
            self.display_results()
    
    def process_dois(self, doi_input: str):
        """Process the entered DOIs"""
        with st.spinner("🔍 Парсинг DOI..."):
            dois = self.system._parse_dois(doi_input)
        
        if not dois:
            st.error("❌ Не найдено валидных DOI")
            return
        
        st.info(f"📚 Найдено {len(dois)} DOI для обработки")
        
        # Create progress containers
        progress_container = st.container()
        results_container = st.container()

        with progress_container:
            st.subheader("📈 Прогресс обработки")
            
            # Main progress с использованием st.empty() для текста
            main_status = st.empty()
            main_progress = st.progress(0, key="main_progress")
            main_status.text("Общий прогресс")
            
            # Individual progress bars с отдельными текстовыми элементами
            analyzed_status = st.empty()
            analyzed_progress = st.progress(0, key="analyzed_progress")
            analyzed_status.text("Анализ статей")
            
            refs_status = st.empty()
            refs_progress = st.progress(0, key="refs_progress")
            refs_status.text("Анализ ссылок")
            
            cites_status = st.empty()
            cites_progress = st.progress(0, key="cites_progress")
            cites_status.text("Анализ цитирований")
            
            insights_status = st.empty()
            insights_progress = st.progress(0, key="insights_progress")
            insights_status.text("Анализ инсайтов")
            
            excel_status = st.empty()
            excel_progress = st.progress(0, key="excel_progress")
            excel_status.text("Создание Excel")
        
        # Вместо повторного вызова render_sidebar(), получаем значение из session_state
        # Если workers_slider еще не установлен, используем значение по умолчанию
        workers = st.session_state.get('workers_slider', Config.DEFAULT_WORKERS)
        
        # Update system settings
        self.system.widgets.workers_slider.value = workers
        
        # Process DOIs
        try:
            start_time = time.time()
            
            # Update main progress
            main_progress.progress(10, text="Начало обработки...")
            main_status.info("🔄 Начинаю обработку DOI...")
            
            # Process analyzed DOIs
            analyzed_progress.progress(0, text="Обработка оригинальных DOI...")
            self.system.analyzed_results = self.system.doi_processor.process_doi_batch(
                dois, "analyzed", None, True, True, Config.BATCH_SIZE, progress_container
            )
            analyzed_progress.progress(100, text="Оригинальные DOI обработаны")
            main_progress.progress(40, text="Оригинальные DOI обработаны")
            
            # Collect and process references
            all_ref_dois = self.system.doi_processor.collect_all_references(self.system.analyzed_results)
            self.system.system_stats['total_ref_dois'] = len(all_ref_dois)
            
            if all_ref_dois:
                main_status.info(f"📎 Найдено {len(all_ref_dois)} reference DOI")
                refs_progress.progress(0, text="Обработка reference DOI...")
                
                ref_dois_to_analyze = all_ref_dois[:5000]
                self.system.ref_results = self.system.doi_processor.process_doi_batch(
                    ref_dois_to_analyze, "ref", None, True, True, Config.BATCH_SIZE, progress_container
                )
                refs_progress.progress(100, text="Reference DOI обработаны")
                main_progress.progress(60, text="Reference DOI обработаны")
            
            # Collect and process citations
            all_cite_dois = self.system.doi_processor.collect_all_citations(self.system.analyzed_results)
            self.system.system_stats['total_cite_dois'] = len(all_cite_dois)
            
            if all_cite_dois:
                main_status.info(f"🔗 Найдено {len(all_cite_dois)} citation DOI")
                cites_progress.progress(0, text="Обработка citation DOI...")
                
                cite_dois_to_analyze = all_cite_dois[:5000]
                self.system.citing_results = self.system.doi_processor.process_doi_batch(
                    cite_dois_to_analyze, "citing", None, True, True, Config.BATCH_SIZE, progress_container
                )
                cites_progress.progress(100, text="Citation DOI обработаны")
                main_progress.progress(80, text="Citation DOI обработаны")
            
            # Retry failed DOIs
            failed_stats = self.system.failed_tracker.get_stats()
            if failed_stats['total_failed'] > 0:
                main_status.info(f"🔄 Повторная обработка {failed_stats['total_failed']} неудачных DOI")
                self.system.doi_processor.retry_failed_dois(self.system.failed_tracker, progress_container=progress_container)
            
            # Generate insights
            insights_progress.progress(0, text="Генерация инсайтов...")
            # Insights are generated during export
            insights_progress.progress(100, text="Инсайты сгенерированы")
            main_progress.progress(90, text="Инсайты сгенерированы")
            
            # Store processed data
            st.session_state.processed_data = {
                'analyzed': self.system.analyzed_results,
                'ref': self.system.ref_results,
                'citing': self.system.citing_results,
                'stats': self.system.system_stats
            }
            
            processing_time = time.time() - start_time
            
            # Update counters
            for doi, result in self.system.analyzed_results.items():
                if result.get('status') == 'success':
                    self.system.excel_exporter.update_counters(
                        result.get('references', []), 
                        result.get('citations', []),
                        "analyzed"
                    )
            
            main_progress.progress(100, text="Обработка завершена!")
            main_status.success(f"✅ Обработка завершена за {processing_time:.1f} секунд!")
            
            # Clear progress bars
            time.sleep(1)
            main_progress.empty()
            analyzed_progress.empty()
            refs_progress.empty()
            cites_progress.empty()
            insights_progress.empty()
            excel_progress.empty()
            main_status.empty()
            
            st.rerun()
            
        except Exception as e:
            st.error(f"❌ Ошибка обработки: {str(e)}")
            import traceback
            st.code(traceback.format_exc())
    
    def export_to_excel(self):
        """Export results to Excel"""
        if not st.session_state.processed_data:
            st.error("Нет данных для экспорта")
            return
        
        with st.spinner("📊 Создание Excel отчета..."):
            excel_data = self.system.excel_exporter.create_comprehensive_report(
                st.session_state.processed_data['analyzed'],
                st.session_state.processed_data['ref'],
                st.session_state.processed_data['citing'],
                st.session_state.analysis_types
            )
            
            st.session_state.excel_file = excel_data
            
            # Create download button
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = f"article_analysis_{timestamp}.xlsx"
            
            st.download_button(
                label="📥 Скачать Excel файл",
                data=excel_data,
                file_name=filename,
                mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet"
            )
            
            st.success("✅ Excel отчет создан!")
    
    def display_results(self):
        """Display processing results"""
        if not st.session_state.processed_data:
            return
        
        st.subheader("📋 Результаты обработки")
        
        data = st.session_state.processed_data
        analyzed_results = data['analyzed']
        
        # Display summary statistics
        successful_count = sum(1 for r in analyzed_results.values() if r.get('status') == 'success')
        failed_count = len(analyzed_results) - successful_count
        
        col1, col2, col3 = st.columns(3)
        with col1:
            st.metric("✅ Успешно", successful_count)
        with col2:
            st.metric("❌ Ошибки", failed_count)
        with col3:
            success_rate = (successful_count / len(analyzed_results) * 100) if analyzed_results else 0
            st.metric("📈 Успешность", f"{success_rate:.1f}%")
        
        # Display detailed results
        with st.expander("📊 Детальная статистика", expanded=False):
            if successful_count > 0:
                total_authors = sum(len(r.get('authors', [])) for r in analyzed_results.values() if r.get('status') == 'success')
                total_refs = sum(len(r.get('references', [])) for r in analyzed_results.values() if r.get('status') == 'success')
                total_cites = sum(len(r.get('citations', [])) for r in analyzed_results.values() if r.get('status') == 'success')
                
                st.info(f"👥 Всего авторов: {total_authors}")
                st.info(f"📎 Всего ссылок: {total_refs}")
                st.info(f"🔗 Всего цитирований: {total_cites}")
            
            if data['ref']:
                ref_success = sum(1 for r in data['ref'].values() if r.get('status') == 'success')
                st.info(f"📎 Reference DOI: {ref_success}/{len(data['ref'])} успешно")
            
            if data['citing']:
                cite_success = sum(1 for r in data['citing'].values() if r.get('status') == 'success')
                st.info(f"🔗 Citation DOI: {cite_success}/{len(data['citing'])} успешно")
        
        # Display individual results
        with st.expander("📄 Детали по статьям", expanded=False):
            tabs = st.tabs(["✅ Успешные", "❌ Ошибки"])
            
            with tabs[0]:
                successful_articles = [(doi, r) for doi, r in analyzed_results.items() if r.get('status') == 'success']
                for doi, result in successful_articles[:10]:  # Show first 10
                    self.display_article_card(result, "analyzed")
                
                if len(successful_articles) > 10:
                    st.info(f"... и еще {len(successful_articles) - 10} успешных статей")
            
            with tabs[1]:
                failed_articles = [(doi, r) for doi, r in analyzed_results.items() if r.get('status') != 'success']
                for doi, result in failed_articles[:5]:  # Show first 5 errors
                    self.display_error_card(doi, result, "analyzed")
                
                if len(failed_articles) > 5:
                    st.info(f"... и еще {len(failed_articles) - 5} ошибок")
    
    def display_article_card(self, result: Dict, source_type: str):
        """Display an article card"""
        pub_info = result['publication_info']
        source_badge = {
            "analyzed": ("📚", "#4CAF50"),
            "ref": ("📎", "#2196F3"),
            "citing": ("🔗", "#9C27B0")
        }.get(source_type, ("📄", "#666"))
        
        quick_insights = result.get('quick_insights', {})
        insight_badge = ""
        if quick_insights:
            citation_velocity = quick_insights.get('citation_velocity', 0)
            if citation_velocity > 20:
                insight_badge = " ⚠️"
            elif citation_velocity > 10:
                insight_badge = " ℹ️"
        
        st.markdown(f"""
        <div style="background: #e8f5e9; padding: 12px; border-radius: 6px; margin: 8px 0; border-left: 4px solid {source_badge[1]};">
            <div style="display: flex; justify-content: space-between; align-items: flex-start;">
                <div style="flex: 1;">
                    <h4 style="margin: 0 0 8px 0; color: #2e7d32; font-size: 14px;">
                        {source_badge[0]} {pub_info.get('title', '')[:70]}{'...' if len(pub_info.get('title', '')) > 70 else ''}{insight_badge}
                    </h4>
                    <div style="font-size: 12px; color: #555; line-height: 1.4;">
                        <strong>DOI:</strong> {result['doi']}<br>
                        <strong>Журнал:</strong> {pub_info.get('journal', '')[:50]}{'...' if len(pub_info.get('journal', '')) > 50 else ''}<br>
                        <strong>Год:</strong> {pub_info.get('year', '')} | 
                        <strong>Авторов:</strong> {len(result.get('authors', []))}<br>
                        <strong>Цитирования:</strong> 
                        <span style="color: {'green' if pub_info.get('citation_count_crossref', 0) > 0 else '#999'}">Crossref: {pub_info.get('citation_count_crossref', 0)}</span> | 
                        <span style="color: {'green' if pub_info.get('citation_count_openalex', 0) > 0 else '#999'}">OpenAlex: {pub_info.get('citation_count_openalex', 0)}</span>
                    </div>
                </div>
                <span style="background: {source_badge[1]}; color: white; padding: 2px 8px; border-radius: 12px; font-size: 11px; font-weight: bold;">
                    {source_type.upper()}
                </span>
            </div>
        </div>
        """, unsafe_allow_html=True)
    
    def display_error_card(self, doi: str, result: Dict, source_type: str):
        """Display an error card"""
        source_badge = {
            "analyzed": ("📚", "#f44336"),
            "ref": ("📎", "#f44336"),
            "citing": ("🔗", "#f44336")
        }.get(source_type, ("📄", "#f44336"))
        
        st.markdown(f"""
        <div style="background: #ffebee; padding: 12px; border-radius: 6px; margin: 8px 0; border-left: 4px solid {source_badge[1]};">
            <div style="display: flex; justify-content: space-between; align-items: center;">
                <div>
                    <h4 style="margin: 0 0 4px 0; color: #c62828; font-size: 14px;">{source_badge[0]} ❌ Ошибка обработки</h4>
                    <div style="font-size: 12px; color: #555;">
                        <strong>DOI:</strong> {doi}
                    </div>
                </div>
                <span style="background: {source_badge[1]}; color: white; padding: 2px 8px; border-radius: 12px; font-size: 11px; font-weight: bold;">
                    {source_type.upper()}
                </span>
            </div>
            
            <div style="margin-top: 8px; padding: 8px; background: #ffcdd2; border-radius: 4px; font-size: 11px;">
                <strong>Причина:</strong> {result.get('error', 'Неизвестная ошибка')}
            </div>
        </div>
        """, unsafe_allow_html=True)

# ============================================================================
# 🚀 ГЛАВНЫЙ КЛАСС СИСТЕМЫ (АДАПТИРОВАННЫЙ ДЛЯ STREAMLIT)
# ============================================================================

class ArticleAnalyzerSystem:
    def __init__(self):
        # Initialize components
        self.cache_manager = SmartCacheManager()
        self.delay_manager = AdaptiveDelayManager()
        self.failed_tracker = FailedDOITracker()
        
        # Initialize API clients
        self.crossref_client = CrossrefClient(self.cache_manager, self.delay_manager)
        self.openalex_client = OpenAlexClient(self.cache_manager, self.delay_manager)
        self.ror_client = RORClient(self.cache_manager)
        
        # Initialize processors
        self.data_processor = DataProcessor(self.cache_manager)
        self.doi_processor = OptimizedDOIProcessor(
            self.cache_manager, self.delay_manager, 
            self.data_processor, self.failed_tracker
        )
        self.hierarchical_analyzer = HierarchicalDataAnalyzer(
            self.cache_manager, self.data_processor, self.doi_processor
        )
        self.excel_exporter = ExcelExporter(self.data_processor, self.ror_client, self.failed_tracker)
        self.excel_exporter.set_hierarchical_analyzer(self.hierarchical_analyzer)
        
        # Streamlit interface
        self.interface_manager = StreamlitInterfaceManager(self)
        
        # System stats
        self.system_stats = {
            'total_dois_processed': 0,
            'total_successful': 0,
            'total_failed': 0,
            'total_authors': 0,
            'total_requests': 0,
            'total_ref_dois': 0,
            'total_cite_dois': 0
        }
        
        # Results storage
        self.analyzed_results = {}
        self.ref_results = {}
        self.citing_results = {}
        
        # Widgets compatibility (minimal)
        self.widgets = type('obj', (object,), {
            'workers_slider': type('obj', (object,), {'value': Config.DEFAULT_WORKERS})()
        })()
    
    def _parse_dois(self, input_text: str) -> List[str]:
        """Parse DOIs from input text"""
        if not input_text:
            return []
        
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
        
        return list(set(dois))
    
    def _clean_doi(self, doi: str) -> str:
        """Clean DOI string"""
        if not doi or not isinstance(doi, str):
            return ""
        
        doi = doi.strip()
        prefixes = ['doi:', 'DOI:', 'https://doi.org/', 'http://doi.org/', 
                   'https://dx.doi.org/', 'http://dx.doi.org/']
        
        for prefix in prefixes:
            if doi.lower().startswith(prefix.lower()):
                doi = doi[len(prefix):]
        
        return doi.strip()

    def run(self):
        """Run the Streamlit application"""
        # Set page config
        st.set_page_config(
            page_title="Анализатор научных статей",
            page_icon="📚",
            layout="wide",
            initial_sidebar_state="expanded"
        )
        
        # Initialize system
        if not st.session_state.get('system_initialized', False):
            with st.spinner("Инициализация системы..."):
                self.cache_manager._clean_expired_cache()
                st.session_state.system_initialized = True
        
        # Render interface - render_sidebar() сохранит значение в session_state
        self.interface_manager.render_sidebar()  # Не присваиваем результат
        self.interface_manager.render_main_interface()

# ============================================================================
# 🏃‍♂️ ЗАПУСК ПРИЛОЖЕНИЯ STREAMLIT
# ============================================================================

if __name__ == "__main__":
    # Create and run the system
    system = ArticleAnalyzerSystem()

    system.run()

