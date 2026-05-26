import tkinter as tk
from tkinter import ttk, messagebox
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.figure import Figure
import matplotlib.animation as animation
from matplotlib.patches import Circle, Rectangle, Polygon
from matplotlib.ticker import FuncFormatter
import matplotlib as mpl
import matplotlib.transforms as transforms
import os
from tkinter import filedialog
import json
import pygame
import wave
import contextlib
from moviepy import VideoFileClip, AudioFileClip, ImageSequenceClip
import tempfile
import shutil
import time
import traceback
import concurrent.futures
from queue import Queue
from PIL import Image

# 配置moviepy使用imageio_ffmpeg（对打包后的exe很重要）
try:
    from imageio_ffmpeg import get_ffmpeg_exe
    os.environ['IMAGEIO_FFMPEG_EXE'] = get_ffmpeg_exe()
except:
    pass  # 如果失败，moviepy会尝试使用系统ffmpeg

class AnimationLoop:
    def __init__(self, app):
        self.app = app
        self.running = False
        self.after_id = None
        self.animation_start_time = None  # 动画开始的绝对时间
        self.animation_start_second = 0  # 动画开始时的current_second
        self.frame_count = 0
        self.fps_start_time = None
        self.target_fps = 15  # 目标刷新率（平衡流畅度和音频质量）
        self.update_interval = 1000 // self.target_fps  # 更新间隔
        self.audio_started = False  # 添加标志位，用于跟踪音频是否已开始播放
        self.audio_start_time = None  # 音频开始播放的时间戳

    def start(self):
        if not self.running:
            print("🎬 动画循环开始")
            self.running = True
            # 记录动画开始的绝对时间和起始秒数
            self.animation_start_time = self.app.root.tk.call('clock', 'milliseconds')
            self.animation_start_second = self.app.current_second
            self.fps_start_time = self.animation_start_time
            self.frame_count = 0
            self.audio_started = False  # 重置音频播放状态
            self.audio_start_time = None  # 重置音频开始时间
            print(f"   起始时间: {self.animation_start_second:.2f}秒")
            self._update()

    def stop(self):
        if self.running:
            print("⏸️ 动画循环停止")
            self.running = False
            if self.after_id:
                self.app.root.after_cancel(self.after_id)
                self.after_id = None
            # 暂停音频播放
            if self.app.audio_file:
                pygame.mixer.music.pause()
            self.audio_started = False  # 重置音频播放状态
            self.audio_start_time = None

    def _update(self):
        if not self.running:
            return

        # 如果用户正在拖动时间轴，暂停动画时间更新，但保持循环运行
        if self.app.is_user_dragging_timeline:
            # 用户正在拖动，重置动画起始时间以避免时间跳跃
            self.animation_start_time = self.app.root.tk.call('clock', 'milliseconds')
            self.animation_start_second = self.app.current_second
            if hasattr(self, 'last_sync_check'):
                self.last_sync_check = self.animation_start_time
            # 继续循环，但不更新时间
            if self.running:
                self.after_id = self.app.root.after(self.update_interval, self._update)
            return

        # 获取当前真实时间
        current_time = self.app.root.tk.call('clock', 'milliseconds')
        
        # 计算从动画开始经过的真实时间（秒）
        elapsed_real_time = (current_time - self.animation_start_time) / 1000.0
        
        # 根据播放速度计算当前应该在的动画时间
        target_second = self.animation_start_second + (elapsed_real_time * self.app.playback_speed)
        
        # 检查是否到达终点
        if target_second >= self.app.total_seconds:
            target_second = self.app.total_seconds - 0.01
            self.app.current_second = target_second
            self.app.current_frame = int(self.app.current_second * self.app.fps)
            self.app.current_frame = max(0, min(self.app.current_frame, self.app.total_frames - 1))
            
            # 更新UI
            self._update_ui()
            
            # 停止播放
            self.stop()
            self.app.is_playing = False
            self.app.fixed_view_range = None
            print("✅ 动画播放完成")
            return
        
        # 更新当前时间
        self.app.current_second = target_second
        self.app.current_frame = int(self.app.current_second * self.app.fps)
        self.app.current_frame = max(0, min(self.app.current_frame, self.app.total_frames - 1))
        if len(self.app.text_box["contents"]) > 0:
            self.app.current_frame = min(self.app.current_frame, len(self.app.text_box["contents"]) - 1)
        
        # 音频同步处理 - 极简版，最小化同步次数以避免卡顿
        if self.app.audio_file:
            if not self.audio_started:
                # 首次启动音频
                try:
                    pygame.mixer.music.play(loops=0, start=self.app.current_second)
                    self.audio_started = True
                    self.audio_start_time = current_time
                    print(f"🎵 音频开始播放，起始位置: {self.app.current_second:.2f}秒")
                    # 初始化同步检查时间
                    self.last_sync_check = current_time
                except Exception as e:
                    print(f"⚠️ 音频播放启动失败: {e}")
                    self.audio_started = False
            elif hasattr(self, 'last_sync_check') and (current_time - self.last_sync_check > 15000):
                # 每15秒检查一次音频同步（降低频率）
                audio_elapsed = (current_time - self.audio_start_time) / 1000.0 * self.app.playback_speed
                expected_position = self.animation_start_second + audio_elapsed
                position_diff = abs(self.app.current_second - expected_position)
                
                # 只有偏差超过1.0秒才重新同步（更大容差以减少卡顿）
                if position_diff > 1.0:
                    try:
                        # 简单直接的同步方式（不使用fadeout避免延迟）
                        current_volume = pygame.mixer.music.get_volume()
                        pygame.mixer.music.stop()
                        pygame.mixer.music.set_volume(current_volume)  # 恢复音量
                        pygame.mixer.music.play(loops=0, start=self.app.current_second)
                        self.audio_start_time = current_time
                        print(f"🔄 音频重新同步到 {self.app.current_second:.2f}秒 (偏差: {position_diff:.2f}s)")
                    except Exception as e:
                        print(f"⚠️ 音频同步失败: {e}")
                self.last_sync_check = current_time
            elif not hasattr(self, 'last_sync_check'):
                self.last_sync_check = current_time
        
        # 更新UI
        self._update_ui()
        
        # FPS统计
        self.frame_count += 1
        if current_time - self.fps_start_time >= 1000:
            actual_fps = self.frame_count
            self.frame_count = 0
            self.fps_start_time = current_time
            # 显示时间偏差（用于调试）
            time_diff = self.app.current_second - target_second
            print(f"📊 刷新率: {actual_fps} FPS | 当前时间: {self.app.current_second:.2f}s | 偏差: {abs(time_diff)*1000:.1f}ms")
        
        # 计算下一次更新的延迟，动态调整以保持同步
        next_delay = self.update_interval
        
        # 安排下一帧
        if self.running:
            self.after_id = self.app.root.after(next_delay, self._update)
    
    def _update_ui(self):
        """更新UI显示"""
        # 更新时间轴滑块（如果用户没有在拖动的话）
        if not self.app.is_user_dragging_timeline:
            self.app.is_time_scale_updating = True
            self.app.time_scale.set(self.app.current_second)
            self.app.is_time_scale_updating = False
        
        # 清理临时关键帧
        self.app.cleanup_temp_keyframes_on_time_change()
        
        # 更新舞台预览
        self.app.update_stage_preview()

class StageAnimationTool:
    def __init__(self, root):
        # 初始化pygame音频 - 优化参数以减少卡顿
        # frequency: 44100Hz (标准音频采样率)
        # size: -16 (16位音频，有符号)
        # channels: 2 (立体声)
        # buffer: 4096 (适中的缓冲区大小，平衡延迟和流畅度)
        # allowedchanges: 允许频率和声道数变化以支持更多格式的WAV文件
        pygame.mixer.quit()  # 先退出以确保干净初始化
        
        # 尝试不同的buffer大小，从最优到备选
        buffer_sizes = [4096, 2048, 8192, 16384]
        initialized = False
        
        for buffer in buffer_sizes:
            try:
                pygame.mixer.init(
                    frequency=44100, 
                    size=-16, 
                    channels=2, 
                    buffer=buffer,
                    allowedchanges=pygame.AUDIO_ALLOW_FREQUENCY_CHANGE | pygame.AUDIO_ALLOW_CHANNELS_CHANGE
                )
                print(f"[OK] 音频系统初始化成功 (buffer={buffer})")
                initialized = True
                break
            except Exception as e:
                print(f"[警告] buffer={buffer} 初始化失败: {e}")
                continue
        
        if not initialized:
            # 如果所有尝试都失败，使用默认参数
            pygame.mixer.init()
            print("[警告] 使用默认音频参数初始化")
        
        pygame.mixer.music.set_volume(1.0)  # 先设置为最大音量，后续再调整
        
        # 设置matplotlib中文字体
        plt.rcParams['font.sans-serif'] = ['SimHei']  # 用来正常显示中文标签
        plt.rcParams['axes.unicode_minus'] = False  # 用来正常显示负号
        # 关闭matplotlib默认网格，使用自定义辅助线
        plt.rcParams['axes.grid'] = False
        
        self.root = root
        self.root.title("舞台走位动画制作工具 v2.8")
        
        # 设置窗口最小尺寸，避免内容变化导致窗口跳动
        self.root.minsize(1400, 800)
        
        # 设置窗口初始大小（不指定位置，让系统自动决定）
        # 不使用 geometry() 设置位置，避免后续操作导致窗口跳动
        # self.root.geometry("1400x900")
        
        # 让窗口在屏幕上居中显示
        window_width = 1400
        window_height = 900
        screen_width = self.root.winfo_screenwidth()
        screen_height = self.root.winfo_screenheight()
        x = (screen_width - window_width) // 2
        y = (screen_height - window_height) // 2
        # 只在首次启动时设置位置，之后不再修改
        self.root.geometry(f"{window_width}x{window_height}+{x}+{y}")
        
        # 添加标志，表示窗口已经初始化完成
        self.window_initialized = False  # 将在 UI 创建完成后设置为 True
        
        # 音频相关属性
        self.audio_file = None
        self.audio_duration = 0
        self.audio_volume = 0.5  # 默认音量为50%
        pygame.mixer.music.set_volume(self.audio_volume)  # 设置初始音量
        
        # 舞台参数
        self.stage_width = 20
        self.stage_height = 15
        
        # 动画控制
        self.fps = 60  # 每秒帧数
        self.total_seconds = 10  # 初始总秒数
        self.total_frames = int(self.total_seconds * self.fps)  # 总帧数
        self.current_frame = 0
        self.current_second = 0
        self.playback_speed = 1.0  # 添加播放速度属性
        self.speed_options = [0.25, 0.5, 0.75, 1.0, 1.5, 2.0, 3.0, 4.0]  # 预设速度选项
        
        # 存储旧版文本框信息（向后兼容）
        self.text_box = {
            "contents": ["" for _ in range(self.total_frames)],  # 初始化为总帧数长度
            "font_size": 12,
            "position": (0, self.stage_height + 1.5),
            "durations": {}  # 存储每个时间点的持续时间：{start_frame: duration_frames}
        }
        
        # 新版文本框系统 - 支持多个独立文本框对象
        self.textboxes = []  # 文本框列表，每个文本框类似演员/道具结构
        
        # 存储演员和道具信息
        self.actors = []
        self.props = []
        
        # 拖动状态
        self.dragging = False
        self.drag_item = None
        self.drag_type = None  # 'actor' 或 'prop'
        self.drag_index = None
        self.drag_offset = None  # 拖动偏移量
        self.drag_start_pos = None
        self.drag_end_pos = None
        self.last_dragged_item = None  # 保存最后拖动的项目
        self.last_dragged_pos = None   # 保存最后拖动的位置
        
        # 多选功能
        self.selected_items = []  # 存储选中的多个对象 [{item, type, index, start_pos}]
        self.multi_select_start_mouse_pos = None  # 多选拖动开始时的鼠标位置
        self.pending_deselect_item = None  # 待取消选中的对象（仅当未拖动时才取消）
        
        # 循环选择重叠对象功能
        self.last_click_pos = None  # 上次点击位置 (x, y)
        self.overlap_candidates = []  # 当前位置的重叠对象候选列表
        self.overlap_current_index = 0  # 当前选中的候选对象索引
        self.click_position_tolerance = 0.3  # 判断是否在同一位置的容差
        
        # 复制粘贴功能
        self.clipboard = []  # 存储复制的对象列表
        self.last_mouse_pos = (0, 0)  # 记录最后的鼠标位置，用于粘贴
        self.style_clipboard = None  # 存储复制的样式数据
        
        # 矩形框选功能
        self.rect_selecting = False  # 是否正在进行矩形框选
        self.rect_select_start = None  # 矩形框选起始点 (x, y)
        self.rect_select_end = None  # 矩形框选结束点 (x, y)
        
        # 智能对齐吸附功能
        self.snap_threshold = 0.5  # 吸附阈值（距离小于此值时吸附）
        self.align_guides = []  # 对齐辅助线列表 [(x1, y1, x2, y2, 'type')]
        
        # 自定义辅助线功能
        self.grid_enabled = tk.BooleanVar(value=True)  # 辅助线开关，默认开启
        # X/Y轴间隔默认值为5
        self.grid_interval_x = 5.0  # X轴间隔
        self.grid_interval_y = 5.0  # Y轴间隔
        self.grid_linestyle = '--'  # 线形：'--'虚线, '-'实线, ':'点线, '-.'点划线
        self.grid_linewidth = 0.5  # 线宽
        self.grid_color = 'black'  # 颜色
        self.grid_alpha = 0.3  # 透明度
        
        # 时间轴控制
        self.is_time_scale_updating = False  # 添加标志位防止递归
        self.is_user_dragging_timeline = False  # 标志位：用户是否正在拖动时间轴
        self.snap_interval = 1.0  # 滑块吸附间隔，默认1秒
        
        # 临时位置覆盖机制
        self.temp_position_overrides = {}  # 用于存储临时位置覆盖
        
        # 临时关键帧管理
        self.temp_keyframes = {}  # 存储临时关键帧 {(element_id, frame): True}
        
        # 固定视图范围 - 用于播放期间保持视图不变
        self.fixed_view_range = None  # 格式: {'xlim': (xmin, xmax), 'ylim': (ymin, ymax)}
        self.is_playing = False  # 播放状态标志
        
        # 缩放控制
        self.zoom_scale = 1.0  # 缩放比例，1.0表示原始大小
        self.min_zoom = 0.3  # 最小缩放比例（30%）
        self.max_zoom = 3.0  # 最大缩放比例（300%）
        self.actual_view_scale = 1.0  # 实际的视图缩放比例（基于视图范围计算）
        
        # 视图平移控制
        self.pan_active = False  # 是否正在平移视图
        self.pan_start = None  # 平移起始位置（数据坐标）
        self.view_center = None  # 视图中心位置（用于平移后保持）
        
        # 撤销/重做历史记录系统
        self.history_stack = []  # 历史状态栈，最多保存20个状态
        self.redo_stack = []  # 重做栈，用于Ctrl+Y重做
        self.max_history = 20  # 最大历史记录数
        self._drag_history_saved = False  # 拖动历史保存标志
        
        # 颜色映射字典
        self.color_map = {
            "红色": "red",
            "蓝色": "blue",
            "绿色": "green",
            "紫色": "purple",
            "橙色": "orange",
            "棕色": "brown"
        }
        
        # 道具形状映射字典（中文到英文）
        self.prop_shape_map = {
            "矩形": "rectangle",
            "圆形": "circle",
            "三角形": "triangle"
        }
        
        # 创建主框架
        self.main_frame = ttk.Frame(root)
        self.main_frame.pack(fill=tk.BOTH, expand=True)
        
        # 创建控制面板
        self.create_control_panel()
        
        # 创建舞台预览
        self.create_stage_preview()
        
        # 创建时间轴
        self.create_timeline()
        
        # 添加动画循环
        self.animation_loop = AnimationLoop(self)
        
        # 绑定窗口关闭事件
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)
        
        # 绑定Ctrl+Z撤销快捷键
        self.root.bind('<Control-z>', self.undo_last_operation)
        self.root.bind('<Control-Z>', self.undo_last_operation)
        
        # 绑定Ctrl+Y重做快捷键
        self.root.bind('<Control-y>', self.redo_last_operation)
        self.root.bind('<Control-Y>', self.redo_last_operation)
        
        # 绑定旋转快捷键（Q逆时针，E顺时针）
        self.root.bind('q', lambda e: self.quick_rotate(-15))
        self.root.bind('Q', lambda e: self.quick_rotate(-15))
        self.root.bind('e', lambda e: self.quick_rotate(15))
        self.root.bind('E', lambda e: self.quick_rotate(15))
        
        # 显示欢迎消息
        self.log("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━", 'info')
        self.log("舞台走位动画制作工具 v2.8", 'info')
        self.log("音频支持：WAV/MP3", 'info')
        self.log("快捷键：Ctrl+Z撤销 | Ctrl+Y重做 | 空格播放/暂停", 'info')
        self.log("快捷键：Ctrl+C / Ctrl+V复制对象 | Delete删除对象", 'info')
        self.log("快捷键：Q/E左右旋转15度（选中对象）", 'info')
        self.log("多选：Ctrl+左键点击对象 | Ctrl+左键拖动框选", 'info')
        self.log("视野：滚轮缩放 | 右键拖动画布", 'info')
        self.log("重叠对象：重复点击同一位置可循环选择", 'info')
        self.log("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━", 'info')
        
        # 标记窗口初始化完成
        self.window_initialized = True

    def save_state_to_history(self, operation_name="操作"):
        """保存当前状态到历史记录
        
        Args:
            operation_name: 操作名称，用于调试和显示
        """
        import copy
        
        # 创建当前状态的深拷贝
        state = {
            'operation': operation_name,
            'actors': copy.deepcopy(self.actors),
            'props': copy.deepcopy(self.props),
            'text_box': copy.deepcopy(self.text_box),
            'textboxes': copy.deepcopy(self.textboxes),  # 添加新版文本框系统
            'current_frame': self.current_frame,
            'current_second': self.current_second
        }
        
        # 添加到历史栈
        self.history_stack.append(state)
        
        # 如果超过最大历史记录数，删除最旧的记录
        if len(self.history_stack) > self.max_history:
            self.history_stack.pop(0)
        
        # 清空重做栈（新操作会使重做历史失效）
        self.redo_stack.clear()
        
        print(f"💾 已保存状态: {operation_name} (历史: {len(self.history_stack)}/{self.max_history})")
    
    def restore_state_from_history(self, state):
        """从历史记录恢复状态
        
        Args:
            state: 要恢复的状态字典
        """
        import copy
        
        # 恢复演员、道具和文本框状态
        self.actors = copy.deepcopy(state['actors'])
        self.props = copy.deepcopy(state['props'])
        self.text_box = copy.deepcopy(state['text_box'])
        # 恢复新版文本框系统（兼容旧版历史记录）
        if 'textboxes' in state:
            self.textboxes = copy.deepcopy(state['textboxes'])
        self.current_frame = state['current_frame']
        self.current_second = state['current_second']
        
        # 更新UI
        self.time_scale.set(self.current_second)
        
        # 更新演员和道具列表
        self.keyframe_listbox.delete(0, tk.END)
        for actor in self.actors:
            self.keyframe_listbox.insert(tk.END, f"演员: {actor['name']}")
        for prop in self.props:
            self.keyframe_listbox.insert(tk.END, f"道具: {prop['name']}")
        for textbox in self.textboxes:
            self.keyframe_listbox.insert(tk.END, f"文本框: {textbox['name']}")
        
        # 更新舞台预览
        self.update_stage_preview()
        
        # 刷新关键帧列表
        self.on_keyframe_list_select(None)
        
        print(f"♻️ 已恢复状态: {state['operation']}")
    
    def undo_last_operation(self, event=None):
        """撤销上一步操作 (Ctrl+Z)"""
        if len(self.history_stack) == 0:
            self.log("⚠️ 没有可以撤销的操作", 'warning')
            return
        
        import copy
        
        # 保存当前状态到重做栈
        current_state = {
            'operation': '当前状态',
            'actors': copy.deepcopy(self.actors),
            'props': copy.deepcopy(self.props),
            'text_box': copy.deepcopy(self.text_box),
            'textboxes': copy.deepcopy(self.textboxes),  # 添加新版文本框系统
            'current_frame': self.current_frame,
            'current_second': self.current_second
        }
        self.redo_stack.append(current_state)
        
        # 限制重做栈大小
        if len(self.redo_stack) > self.max_history:
            self.redo_stack.pop(0)
        
        # 弹出最后一个状态（即当前状态之前的状态）
        last_state = self.history_stack.pop()
        
        # 恢复到该状态
        self.restore_state_from_history(last_state)
        
        self.log(f"↶ 已撤销: {last_state['operation']}", 'undo')
        print(f"↶ 撤销完成 (可重做: {len(self.redo_stack)})")
        
        # 返回"break"以阻止事件继续传播
        return "break"
    
    def redo_last_operation(self, event=None):
        """重做上一步撤销的操作 (Ctrl+Y)"""
        if len(self.redo_stack) == 0:
            self.log("⚠️ 没有可以重做的操作", 'warning')
            return
        
        import copy
        
        # 保存当前状态到历史栈
        current_state = {
            'operation': '当前状态',
            'actors': copy.deepcopy(self.actors),
            'props': copy.deepcopy(self.props),
            'text_box': copy.deepcopy(self.text_box),
            'textboxes': copy.deepcopy(self.textboxes),  # 添加新版文本框系统
            'current_frame': self.current_frame,
            'current_second': self.current_second
        }
        self.history_stack.append(current_state)
        
        # 限制历史栈大小
        if len(self.history_stack) > self.max_history:
            self.history_stack.pop(0)
        
        # 弹出重做栈的最后一个状态
        redo_state = self.redo_stack.pop()
        
        # 恢复到该状态
        self.restore_state_from_history(redo_state)
        
        self.log("↷ 已重做上一步撤销的操作", 'undo')
        print(f"↷ 重做完成 (可撤销: {len(self.history_stack)})")
        
        # 返回"break"以阻止事件继续传播
        return "break"
    
    def log(self, message, level='info'):
        """输出日志到日志窗口
        
        Args:
            message: 日志消息
            level: 日志级别 ('info', 'success', 'warning', 'error', 'undo')
        """
        import datetime
        
        # 获取当前时间
        timestamp = datetime.datetime.now().strftime('%H:%M:%S')
        
        # 格式化消息
        formatted_message = f"[{timestamp}] {message}\n"
        
        # 保存当前的yview位置
        current_yview = self.log_text.yview()
        
        # 启用编辑
        self.log_text.config(state='normal')
        
        # 限制日志行数，防止无限增长导致性能问题
        line_count = int(self.log_text.index('end-1c').split('.')[0])
        if line_count > 100:  # 最多保留100行日志
            self.log_text.delete('1.0', '2.0')  # 删除第一行
        
        # 添加日志
        self.log_text.insert(tk.END, formatted_message, level)
        
        # 自动滚动到最后
        self.log_text.see(tk.END)
        
        # 禁用编辑
        self.log_text.config(state='disabled')
        
        # 强制更新idle任务，但不调用update()避免窗口重新布局
        self.log_text.update_idletasks()
        
        # 同时输出到控制台（可选）
        print(formatted_message.strip())
    
    def on_closing(self):
        """处理窗口关闭事件"""
        # 停止音频播放
        if self.audio_file:
            pygame.mixer.music.stop()
        # 退出pygame
        pygame.mixer.quit()
        # 关闭窗口
        self.root.destroy()

    def create_control_panel(self):
        # 创建主控制面板框架，设置固定宽度（优化：减小宽度）
        control_frame = ttk.LabelFrame(self.main_frame, text="控制面板", width=260)
        control_frame.pack(side=tk.LEFT, fill=tk.Y, padx=5, pady=5)
        control_frame.pack_propagate(False)  # 禁止子组件改变父容器大小
        
        # 创建可滚动的Canvas（宽度相应调整）
        self.control_canvas = tk.Canvas(control_frame, width=240, highlightthickness=0)
        scrollbar = ttk.Scrollbar(control_frame, orient="vertical", command=self.control_canvas.yview)
        self.scrollable_frame = ttk.Frame(self.control_canvas)
        
        # 创建窗口对象，固定在顶部
        self.control_canvas_window_id = self.control_canvas.create_window((0, 0), window=self.scrollable_frame, anchor="nw")
        
        # 检查并修正滚动位置，确保不会出现空白
        def check_scroll_position():
            """检查滚动位置，如果超出范围则重置到顶部"""
            try:
                top, bottom = self.control_canvas.yview()
                # 如果滚动位置在顶部之上（小于0或接近0），重置到顶部
                if top <= 0 or abs(top) < 0.001:
                    self.control_canvas.yview_moveto(0)
                    # 确保窗口坐标保持在 (0, 0)
                    self.control_canvas.coords(self.control_canvas_window_id, 0, 0)
            except:
                pass
        
        # 配置滚动区域，确保从 y=0 开始
        def update_scrollregion(event=None):
            bbox = self.control_canvas.bbox("all")
            if bbox:
                # 强制滚动区域从 y=0 开始，防止向上滚动时出现空白
                self.control_canvas.configure(scrollregion=(0, 0, bbox[2], bbox[3]))
                # 更新后检查滚动位置，防止出现空白
                self.control_canvas.after_idle(check_scroll_position)
        
        self.scrollable_frame.bind("<Configure>", update_scrollregion)
        
        # 确保窗口对象宽度适应 Canvas，并始终固定在顶部
        def on_canvas_configure(event):
            self.control_canvas.itemconfig(self.control_canvas_window_id, width=event.width)
            # 强制窗口坐标保持在 (0, 0)，防止滚动时移动
            self.control_canvas.coords(self.control_canvas_window_id, 0, 0)
        
        self.control_canvas.bind("<Configure>", on_canvas_configure)
        
        # 自定义滚动命令，添加边界检查
        def safe_yscrollcommand(*args):
            scrollbar.set(*args)
            # 滚动后检查位置，防止超出范围
            self.control_canvas.after_idle(check_scroll_position)
        
        self.control_canvas.configure(yscrollcommand=safe_yscrollcommand)
        
        # 打包Canvas和滚动条
        self.control_canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        
        # 绑定鼠标滚轮事件，添加位置检查
        def _on_mousewheel(event):
            # 兼容不同操作系统的滚轮事件
            if event.delta:
                # Windows和macOS
                self.control_canvas.yview_scroll(int(-1*(event.delta/120)), "units")
            else:
                # Linux
                if event.num == 4:
                    self.control_canvas.yview_scroll(-1, "units")
                elif event.num == 5:
                    self.control_canvas.yview_scroll(1, "units")
            # 滚动后立即检查位置
            self.control_canvas.after_idle(check_scroll_position)
        
        # 绑定滚轮事件到canvas
        self.control_canvas.bind("<MouseWheel>", _on_mousewheel)  # Windows和macOS
        self.control_canvas.bind("<Button-4>", _on_mousewheel)    # Linux上滚
        self.control_canvas.bind("<Button-5>", _on_mousewheel)    # Linux下滚
        
        # 递归绑定所有子控件的滚轮事件
        def bind_mousewheel_to_children(widget):
            widget.bind("<MouseWheel>", _on_mousewheel)
            widget.bind("<Button-4>", _on_mousewheel)
            widget.bind("<Button-5>", _on_mousewheel)
            for child in widget.winfo_children():
                bind_mousewheel_to_children(child)
        
        # 延迟绑定，确保所有控件都已创建
        def delayed_bind():
            bind_mousewheel_to_children(self.scrollable_frame)
        
        self.control_canvas.after(100, delayed_bind)
        
        # 现在所有控件都添加到self.scrollable_frame而不是control_frame
        
        # 舞台设置与时间轴设置并排显示
        settings_container = ttk.Frame(self.scrollable_frame)
        settings_container.pack(fill=tk.X, padx=5, pady=(0,2))
        
        # 舞台设置
        stage_frame = ttk.LabelFrame(settings_container, text="舞台设置")
        stage_frame.grid(row=0, column=0, padx=(0, 1), pady=0, sticky=tk.N+tk.W+tk.E)
        
        ttk.Label(stage_frame, text="宽:").grid(row=0, column=0, padx=2, pady=1, sticky='e')
        self.width_entry = ttk.Entry(stage_frame, width=7)
        self.width_entry.insert(0, str(self.stage_width))
        self.width_entry.grid(row=0, column=1, padx=2, pady=1)
        
        ttk.Label(stage_frame, text="高:").grid(row=1, column=0, padx=2, pady=1, sticky='e')
        self.height_entry = ttk.Entry(stage_frame, width=7)
        self.height_entry.insert(0, str(self.stage_height))
        self.height_entry.grid(row=1, column=1, padx=2, pady=1)
        
        ttk.Button(stage_frame, text="✓应用", command=self.update_stage_size, width=7).grid(row=2, column=0, columnspan=2, pady=1)
        
        # 时间轴设置
        timeline_frame = ttk.LabelFrame(settings_container, text="时间轴设置")
        timeline_frame.grid(row=0, column=1, padx=(1, 0), pady=0, sticky=tk.N+tk.W+tk.E)
        
        ttk.Label(timeline_frame, text="秒数:").grid(row=0, column=0, padx=2, pady=1, sticky='e')
        self.seconds_entry = ttk.Entry(timeline_frame, width=7)
        self.seconds_entry.insert(0, str(self.total_seconds))
        self.seconds_entry.grid(row=0, column=1, padx=2, pady=1)
        
        ttk.Label(timeline_frame, text="速度:").grid(row=1, column=0, padx=2, pady=1, sticky='e')
        self.speed_var = tk.StringVar(value=str(self.playback_speed))
        self.speed_combo = ttk.Combobox(timeline_frame, textvariable=self.speed_var, 
                                      values=[f"{x:.2f}x" for x in self.speed_options],
                                      width=5, state="readonly")
        self.speed_combo.grid(row=1, column=1, padx=2, pady=1)
        self.speed_combo.bind('<<ComboboxSelected>>', self.on_speed_change)
        
        ttk.Button(timeline_frame, text="✓应用", command=self.update_timeline_settings, width=7).grid(row=2, column=0, columnspan=2, pady=1)
        
        # 配置列权重以实现均匀分布
        settings_container.columnconfigure(0, weight=1)
        settings_container.columnconfigure(1, weight=1)
        
        # 添加演员/道具区域
        add_frame = ttk.LabelFrame(self.scrollable_frame, text="对象设置")
        add_frame.pack(fill=tk.X, padx=5, pady=2)
        
        # 演员设置（紧凑布局）
        actor_frame = ttk.LabelFrame(add_frame, text="👤 演员")
        actor_frame.pack(fill=tk.X, padx=3, pady=1)
        
        # 名称输入框单独一行
        name_frame = ttk.Frame(actor_frame)
        name_frame.pack(fill=tk.X, padx=2, pady=1)
        ttk.Label(name_frame, text="名称:").pack(side=tk.LEFT, padx=(0,1))
        self.actor_name_entry = ttk.Entry(name_frame, width=16)
        self.actor_name_entry.pack(side=tk.LEFT, padx=0)
        ttk.Button(name_frame, text="✓", width=2, command=self.apply_actor_name).pack(side=tk.LEFT, padx=(1,0))
        
        # 使用grid布局，更紧凑（两个输入框的行）
        actor_grid = ttk.Frame(actor_frame)
        actor_grid.pack(fill=tk.X, padx=2, pady=1)
        
        # 大小和字号放在同一行
        ttk.Label(actor_grid, text="大小:").grid(row=0, column=0, sticky='e', padx=(0,1), pady=1)
        self.actor_size_entry = ttk.Entry(actor_grid, width=7)
        self.actor_size_entry.insert(0, "1.0")
        self.actor_size_entry.grid(row=0, column=1, sticky='w', padx=0, pady=1)
        
        ttk.Label(actor_grid, text="字号:").grid(row=0, column=2, sticky='e', padx=(1,1), pady=1)
        self.actor_font_size = ttk.Entry(actor_grid, width=7)
        self.actor_font_size.insert(0, "10")
        self.actor_font_size.grid(row=0, column=3, sticky='w', padx=0, pady=1)
        
        ttk.Label(actor_grid, text="颜色:").grid(row=1, column=0, sticky='e', padx=(0,1), pady=1)
        self.actor_color_var = tk.StringVar(value="蓝色")
        self.actor_color_combo = ttk.Combobox(actor_grid, textvariable=self.actor_color_var, 
                                            values=["蓝色", "红色", "绿色", "紫色", "橙色", "棕色"], 
                                            width=5, state="readonly")
        self.actor_color_combo.grid(row=1, column=1, sticky='w', padx=0, pady=1)
        
        # 配置列权重（移除所有列的扩展以减小两个输入框之间的间距）
        actor_grid.columnconfigure(0, weight=0)
        actor_grid.columnconfigure(1, weight=0, minsize=0)
        actor_grid.columnconfigure(2, weight=0, minsize=1)  # 减小标签列宽度
        actor_grid.columnconfigure(3, weight=0, minsize=0)  # 移除列3的扩展以减小间距
        
        # 隐藏形状选择但保留功能
        self.actor_shape_var = tk.StringVar(value="circle")
        self.actor_shape_combo = ttk.Combobox(actor_frame, textvariable=self.actor_shape_var, 
                                            values=["circle", "square", "triangle"], width=7)
        
        # 操作按钮（极简）
        actor_btn_frame = ttk.Frame(actor_frame)
        actor_btn_frame.pack(fill=tk.X, padx=2, pady=1)
        ttk.Button(actor_btn_frame, text="添加", command=self.add_actor, width=7).pack(side=tk.LEFT, padx=1)
        ttk.Button(actor_btn_frame, text="删除", command=self.delete_actor, width=7).pack(side=tk.LEFT, padx=1)
        
        # 道具设置（紧凑布局）
        prop_frame = ttk.LabelFrame(add_frame, text="🎭 道具")
        prop_frame.pack(fill=tk.X, padx=3, pady=1)
        self.prop_frame_ref = prop_frame
        
        # 名称输入框单独一行
        name_frame = ttk.Frame(prop_frame)
        name_frame.pack(fill=tk.X, padx=2, pady=1)
        ttk.Label(name_frame, text="名称:").pack(side=tk.LEFT, padx=(0,1))
        self.prop_name_entry = ttk.Entry(name_frame, width=16)
        self.prop_name_entry.pack(side=tk.LEFT, padx=0)
        ttk.Button(name_frame, text="✓", width=2, command=self.apply_prop_name).pack(side=tk.LEFT, padx=(1,0))
        
        # 使用grid布局（两个输入框的行）
        prop_grid = ttk.Frame(prop_frame)
        prop_grid.pack(fill=tk.X, padx=2, pady=1)
        
        # 形状和字号放在同一行
        ttk.Label(prop_grid, text="形状:").grid(row=0, column=0, sticky='e', padx=(0,1), pady=1)
        self.prop_shape_var = tk.StringVar(value="矩形")
        self.prop_shape_combo = ttk.Combobox(prop_grid, textvariable=self.prop_shape_var, 
                                           values=["矩形", "圆形", "三角形"], 
                                           width=5, state="readonly")
        self.prop_shape_combo.grid(row=0, column=1, sticky='w', padx=0, pady=1)
        self.prop_shape_combo.bind("<<ComboboxSelected>>", self.on_prop_shape_change)
        
        ttk.Label(prop_grid, text="字号:").grid(row=0, column=2, sticky='e', padx=(1,1), pady=1)
        self.prop_font_size = ttk.Entry(prop_grid, width=7)
        self.prop_font_size.insert(0, "10")
        self.prop_font_size.grid(row=0, column=3, sticky='w', padx=0, pady=1)
        
        # 宽度和高度放在同一行
        self.prop_width_label = ttk.Label(prop_grid, text="宽度:")
        self.prop_width_label.grid(row=1, column=0, sticky='e', padx=(0,1), pady=1)
        self.prop_width_entry = ttk.Entry(prop_grid, width=7)
        self.prop_width_entry.insert(0, "1.0")
        self.prop_width_entry.grid(row=1, column=1, sticky='w', padx=0, pady=1)
        
        self.prop_height_label = ttk.Label(prop_grid, text="高度:")
        self.prop_height_label.grid(row=1, column=2, sticky='e', padx=(1,1), pady=1)
        self.prop_height_entry = ttk.Entry(prop_grid, width=7)
        self.prop_height_entry.insert(0, "1.0")
        self.prop_height_entry.grid(row=1, column=3, sticky='w', padx=0, pady=1)
        
        ttk.Label(prop_grid, text="颜色:").grid(row=2, column=0, sticky='e', padx=(0,1), pady=1)
        self.prop_color_var = tk.StringVar(value="红色")
        self.prop_color_combo = ttk.Combobox(prop_grid, textvariable=self.prop_color_var, 
                                           values=["红色", "蓝色", "绿色", "紫色", "橙色", "棕色"], 
                                           width=5, state="readonly")
        self.prop_color_combo.grid(row=2, column=1, sticky='w', padx=0, pady=1)
        
        # 配置列权重（移除所有列的扩展以减小两个输入框之间的间距）
        prop_grid.columnconfigure(0, weight=0)
        prop_grid.columnconfigure(1, weight=0, minsize=0)
        prop_grid.columnconfigure(2, weight=0, minsize=1)  # 减小标签列宽度
        prop_grid.columnconfigure(3, weight=0, minsize=0)  # 移除列3的扩展以减小间距
        
        # 操作按钮（极简）
        prop_btn_frame = ttk.Frame(prop_frame)
        prop_btn_frame.pack(fill=tk.X, padx=2, pady=1)
        ttk.Button(prop_btn_frame, text="添加", command=self.add_prop, width=7).pack(side=tk.LEFT, padx=1)
        ttk.Button(prop_btn_frame, text="删除", command=self.delete_prop, width=7).pack(side=tk.LEFT, padx=1)
        
        # 新版样式编辑面板（用于演员和道具）- 可折叠
        unified_style_frame = ttk.LabelFrame(add_frame, text="🎨 样式")
        unified_style_frame.pack(fill=tk.X, padx=3, pady=1)
        
        # 展开/收起按钮（放在最前面）
        self.style_detail_expanded = tk.BooleanVar(value=False)
        detail_toggle_btn = ttk.Button(unified_style_frame, text="▶ 展开样式编辑", 
                                       command=self.toggle_style_detail_panel)
        detail_toggle_btn.pack(fill=tk.X, padx=1, pady=1)
        self.style_detail_toggle_btn = detail_toggle_btn
        
        # === 详细编辑面板（可折叠，极简布局） ===
        self.style_detail_panel = ttk.Frame(unified_style_frame)
        
        # 边框详细设置（紧凑多列）
        border_detail = ttk.LabelFrame(self.style_detail_panel, text="边框")
        border_detail.pack(fill=tk.X, padx=1, pady=1)
        
        # 颜色和宽度放在同一行
        ttk.Label(border_detail, text="色:").grid(row=0, column=0, sticky='e', padx=(0,1), pady=1)
        self.style_border_color_var = tk.StringVar(value="蓝色")
        self.style_border_color_combo = ttk.Combobox(border_detail, 
                                               textvariable=self.style_border_color_var,
                                               values=["蓝色", "红色", "绿色", "紫色", "橙色", "棕色"],
                                               width=5, state="readonly")
        self.style_border_color_combo.grid(row=0, column=1, sticky='w', padx=0, pady=1)
        
        ttk.Label(border_detail, text="宽:").grid(row=0, column=2, sticky='e', padx=(1,1), pady=1)
        self.style_border_width = ttk.Entry(border_detail, width=7)
        self.style_border_width.insert(0, "2")
        self.style_border_width.grid(row=0, column=3, sticky='w', padx=0, pady=1)
        
        # 透明度和线形放在第二行
        ttk.Label(border_detail, text="透明:").grid(row=1, column=0, sticky='e', padx=(0,1), pady=1)
        self.style_border_alpha = ttk.Entry(border_detail, width=7)
        self.style_border_alpha.insert(0, "1.0")
        self.style_border_alpha.grid(row=1, column=1, sticky='w', padx=0, pady=1)
        
        ttk.Label(border_detail, text="线形:").grid(row=1, column=2, sticky='e', padx=(1,1), pady=1)
        self.style_border_style_var = tk.StringVar(value="实线")
        self.style_border_style_combo = ttk.Combobox(border_detail, 
                                               textvariable=self.style_border_style_var,
                                               values=["实线", "虚线", "点线", "点划线"],
                                               width=5, state="readonly")
        self.style_border_style_combo.grid(row=1, column=3, sticky='w', padx=0, pady=1)
        
        border_detail.columnconfigure(0, weight=0)
        border_detail.columnconfigure(1, weight=0, minsize=0)  # 移除列1扩展以减小间距
        border_detail.columnconfigure(2, weight=0, minsize=1)  # 减小标签列宽度
        border_detail.columnconfigure(3, weight=0, minsize=0)  # 移除列3扩展以减小间距
        
        # 填充设置（紧凑多列）
        fill_detail = ttk.LabelFrame(self.style_detail_panel, text="填充")
        fill_detail.pack(fill=tk.X, padx=1, pady=1)
        
        self.style_fill_enabled_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(fill_detail, text="启用", variable=self.style_fill_enabled_var).grid(row=0, column=0, columnspan=2, sticky='w', padx=(1,0), pady=1)
        
        # 颜色和透明度放在同一行
        ttk.Label(fill_detail, text="色:").grid(row=1, column=0, sticky='e', padx=(0,1), pady=1)
        self.style_fill_color_var = tk.StringVar(value="蓝色")
        self.style_fill_color_combo = ttk.Combobox(fill_detail, 
                                               textvariable=self.style_fill_color_var,
                                               values=["蓝色", "红色", "绿色", "紫色", "橙色", "棕色"],
                                               width=5, state="readonly")
        self.style_fill_color_combo.grid(row=1, column=1, sticky='w', padx=0, pady=1)
        
        ttk.Label(fill_detail, text="透明:").grid(row=1, column=2, sticky='e', padx=(1,1), pady=1)
        self.style_fill_alpha = ttk.Entry(fill_detail, width=7)
        self.style_fill_alpha.insert(0, "1.0")
        self.style_fill_alpha.grid(row=1, column=3, sticky='w', padx=0, pady=1)
        
        fill_detail.columnconfigure(0, weight=0)
        fill_detail.columnconfigure(1, weight=0, minsize=0)  # 移除列1扩展以减小间距
        fill_detail.columnconfigure(2, weight=0, minsize=1)  # 减小标签列宽度
        fill_detail.columnconfigure(3, weight=0, minsize=0)  # 移除列3扩展以减小间距
        
        # 文本设置（紧凑多列）
        text_detail = ttk.LabelFrame(self.style_detail_panel, text="文本")
        text_detail.pack(fill=tk.X, padx=1, pady=1)
        
        # 颜色和字号放在同一行
        ttk.Label(text_detail, text="色:").grid(row=0, column=0, sticky='e', padx=(0,1), pady=1)
        self.style_text_color_var = tk.StringVar(value="蓝色")
        self.style_text_color_combo = ttk.Combobox(text_detail, 
                                               textvariable=self.style_text_color_var,
                                               values=["蓝色", "红色", "绿色", "紫色", "橙色", "棕色"],
                                               width=5, state="readonly")
        self.style_text_color_combo.grid(row=0, column=1, sticky='w', padx=0, pady=1)
        
        ttk.Label(text_detail, text="字号:").grid(row=0, column=2, sticky='e', padx=(1,1), pady=1)
        self.style_text_size = ttk.Entry(text_detail, width=7)
        self.style_text_size.insert(0, "10")
        self.style_text_size.grid(row=0, column=3, sticky='w', padx=0, pady=1)
        
        # 透明度和文本样式复选框放在第二行
        ttk.Label(text_detail, text="透明:").grid(row=1, column=0, sticky='e', padx=(0,1), pady=1)
        self.style_text_alpha = ttk.Entry(text_detail, width=7)
        self.style_text_alpha.insert(0, "1.0")
        self.style_text_alpha.grid(row=1, column=1, sticky='w', padx=0, pady=1)
        
        # 文本样式复选框
        text_style_frame = ttk.Frame(text_detail)
        text_style_frame.grid(row=1, column=2, columnspan=2, sticky='w', padx=(3,0), pady=1)
        self.style_text_bold_var = tk.BooleanVar(value=False)
        self.style_text_italic_var = tk.BooleanVar(value=False)
        self.style_text_underline_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(text_style_frame, text="粗", variable=self.style_text_bold_var).pack(side=tk.LEFT, padx=1)
        ttk.Checkbutton(text_style_frame, text="斜", variable=self.style_text_italic_var).pack(side=tk.LEFT, padx=1)
        ttk.Checkbutton(text_style_frame, text="下", variable=self.style_text_underline_var).pack(side=tk.LEFT, padx=1)
        
        text_detail.columnconfigure(0, weight=0)
        text_detail.columnconfigure(1, weight=0, minsize=0)  # 移除列1扩展以减小间距
        text_detail.columnconfigure(2, weight=0, minsize=1)  # 减小标签列宽度
        text_detail.columnconfigure(3, weight=0, minsize=0)  # 移除列3扩展以减小间距
        
        # 应用按钮（极简）
        detail_btn_frame = ttk.Frame(self.style_detail_panel)
        detail_btn_frame.pack(fill=tk.X, padx=1, pady=1)
        ttk.Button(detail_btn_frame, text="应用", width=5,
                  command=self.apply_detailed_style).pack(side=tk.LEFT, padx=1)
        ttk.Button(detail_btn_frame, text="复制", width=5,
                  command=self.copy_style).pack(side=tk.LEFT, padx=1)
        ttk.Button(detail_btn_frame, text="粘贴", width=5,
                  command=self.paste_style).pack(side=tk.LEFT, padx=1)
        ttk.Button(detail_btn_frame, text="重置", width=5,
                  command=self.reset_style_to_default).pack(side=tk.LEFT, padx=1)
        
        # 文本框设置（紧凑布局）
        textbox_frame = ttk.LabelFrame(add_frame, text="📝 文本框")
        textbox_frame.pack(fill=tk.X, padx=3, pady=1)
        
        # 名称输入框单独一行
        name_frame = ttk.Frame(textbox_frame)
        name_frame.pack(fill=tk.X, padx=2, pady=1)
        ttk.Label(name_frame, text="名称:").pack(side=tk.LEFT, padx=(0,1))
        self.textbox_name_entry = ttk.Entry(name_frame, width=16)
        self.textbox_name_entry.pack(side=tk.LEFT, padx=0)
        ttk.Button(name_frame, text="✓", width=2, command=self.update_textbox_name).pack(side=tk.LEFT, padx=(1,0))
        
        # 使用grid布局（两个输入框的行）
        tb_grid = ttk.Frame(textbox_frame)
        tb_grid.pack(fill=tk.X, padx=2, pady=1)
        
        # 字号和颜色放在同一行
        ttk.Label(tb_grid, text="字号:").grid(row=0, column=0, sticky='e', padx=(0,1), pady=1)
        self.textbox_font_size = ttk.Entry(tb_grid, width=7)
        self.textbox_font_size.insert(0, "12")
        self.textbox_font_size.grid(row=0, column=1, sticky='w', padx=0, pady=1)
        
        ttk.Label(tb_grid, text="颜色:").grid(row=0, column=2, sticky='e', padx=(1,1), pady=1)
        self.textbox_color_var = tk.StringVar(value="黑色")
        self.textbox_color_combo = ttk.Combobox(tb_grid, textvariable=self.textbox_color_var, 
                                           values=["黑色", "红色", "蓝色", "绿色", "紫色", "橙色"], 
                                           width=5, state="readonly")
        self.textbox_color_combo.grid(row=0, column=3, sticky='w', padx=0, pady=1)
        
        # 开始和结束时间放在同一行
        ttk.Label(tb_grid, text="开始:").grid(row=1, column=0, sticky='e', padx=(0,1), pady=1)
        self.textbox_start_time = ttk.Entry(tb_grid, width=7)
        self.textbox_start_time.insert(0, "0.0")
        self.textbox_start_time.grid(row=1, column=1, sticky='w', padx=0, pady=1)
        self.textbox_start_time.bind('<Double-Button-1>', lambda e: self._fill_current_time(self.textbox_start_time))
        
        ttk.Label(tb_grid, text="结束:").grid(row=1, column=2, sticky='e', padx=(1,1), pady=1)
        self.textbox_end_time = ttk.Entry(tb_grid, width=7)
        self.textbox_end_time.insert(0, "5.0")
        self.textbox_end_time.grid(row=1, column=3, sticky='w', padx=0, pady=1)
        self.textbox_end_time.bind('<Double-Button-1>', lambda e: self._fill_current_time(self.textbox_end_time))
        
        # 配置列权重（移除所有列的扩展以减小两个输入框之间的间距）
        tb_grid.columnconfigure(0, weight=0)
        tb_grid.columnconfigure(1, weight=0, minsize=0)
        tb_grid.columnconfigure(2, weight=0, minsize=1)  # 减小标签列宽度
        tb_grid.columnconfigure(3, weight=0, minsize=0)  # 移除列3的扩展以减小间距
        
        # 内容输入（极简布局）
        content_frame = ttk.Frame(textbox_frame)
        content_frame.pack(fill=tk.X, padx=2, pady=1)
        
        ttk.Label(content_frame, text="内容:").pack(side=tk.LEFT, padx=(1,0), anchor='n')
        
        text_container = ttk.Frame(content_frame)
        text_container.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=1)
        
        self.textbox_content_entry = tk.Text(text_container, width=8, height=2, wrap=tk.WORD, font=('Microsoft YaHei', 9))
        self.textbox_content_entry.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        content_scrollbar = ttk.Scrollbar(text_container, command=self.textbox_content_entry.yview)
        content_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.textbox_content_entry.config(yscrollcommand=content_scrollbar.set)
        
        ttk.Button(content_frame, text="✓", width=2, command=self.update_textbox_content).pack(side=tk.LEFT, padx=(0,1), anchor='n')
        
        # 保存最后一次选中的文本和位置
        self.last_text_selection = ""
        self.last_text_selection_range = None
        self.last_selected_textbox_for_ui = None
        
        # 更新显示标签的函数
        def update_selection_display(event=None):
            if self.last_text_selection:
                display_text = self.last_text_selection[:8] + ".." if len(self.last_text_selection) > 8 else self.last_text_selection
                self.selected_text_label.config(text=display_text, foreground='red')
            else:
                self.selected_text_label.config(text='全部', foreground='blue')
        
        # 绑定到内容框的选中事件
        def enhanced_save_selection(event=None):
            try:
                if self.textbox_content_entry.tag_ranges(tk.SEL):
                    self.last_text_selection = self.textbox_content_entry.get(tk.SEL_FIRST, tk.SEL_LAST)
                    char_start = len(self.textbox_content_entry.get("1.0", tk.SEL_FIRST))
                    char_end = len(self.textbox_content_entry.get("1.0", tk.SEL_LAST))
                    self.last_text_selection_range = (char_start, char_end)
                    update_selection_display()
                else:
                    self.last_text_selection = ""
                    self.last_text_selection_range = None
                    update_selection_display()
            except tk.TclError:
                self.last_text_selection = ""
                self.last_text_selection_range = None
                update_selection_display()
        
        # 绑定选中事件
        self.textbox_content_entry.bind('<<Selection>>', enhanced_save_selection)
        self.textbox_content_entry.bind('<ButtonRelease-1>', enhanced_save_selection)
        self.textbox_content_entry.bind('<B1-Motion>', enhanced_save_selection)
        self.textbox_content_entry.bind('<KeyRelease>', enhanced_save_selection)
        
        # 选中文本显示（紧凑）
        select_frame = ttk.Frame(textbox_frame)
        select_frame.pack(fill=tk.X, padx=2, pady=1)
        ttk.Label(select_frame, text="选中:", font=('Arial', 8), foreground='gray').pack(side=tk.LEFT, padx=2)
        self.selected_text_label = ttk.Label(select_frame, text="全部", font=('Arial', 8), foreground='blue')
        self.selected_text_label.pack(side=tk.LEFT, padx=2)
        
        # 清除选择按钮
        def clear_selection():
            self.last_text_selection = ""
            self.last_text_selection_range = None
            self.selected_text_label.config(text='全部', foreground='blue')
        
        # 操作按钮（合并到一行）
        textbox_btn_frame = ttk.Frame(textbox_frame)
        textbox_btn_frame.pack(fill=tk.X, padx=2, pady=1)
        
        ttk.Button(textbox_btn_frame, text="添加", command=self.add_textbox, width=5).pack(side=tk.LEFT, padx=1)
        ttk.Button(textbox_btn_frame, text="删除", command=self.delete_textbox, width=5).pack(side=tk.LEFT, padx=1)
        ttk.Button(textbox_btn_frame, text="应用", width=5, 
                  command=self.apply_textbox_all_styles).pack(side=tk.LEFT, padx=1)
        ttk.Button(textbox_btn_frame, text="清除", width=5, command=clear_selection).pack(side=tk.LEFT, padx=1)
        
        # 辅助线设置（极简布局）
        grid_frame = ttk.LabelFrame(add_frame, text="📏 辅助线")
        grid_frame.pack(fill=tk.X, padx=3, pady=1)
        
        # 使用grid布局
        grid_g = ttk.Frame(grid_frame)
        grid_g.pack(fill=tk.X, padx=2, pady=1)
        
        self.grid_switch = ttk.Checkbutton(grid_g, text="启用", 
                                          variable=self.grid_enabled,
                                          command=self.update_stage_preview)
        self.grid_switch.grid(row=0, column=0, columnspan=2, sticky='w', padx=(1,0), pady=1)
        
        # X和Y间隔放在同一行
        ttk.Label(grid_g, text="X:").grid(row=1, column=0, sticky='e', padx=(0,1), pady=1)
        self.grid_x_entry = ttk.Entry(grid_g, width=7)
        self.grid_x_entry.insert(0, "5.0")
        self.grid_x_entry.grid(row=1, column=1, sticky='w', padx=0, pady=1)
        
        ttk.Label(grid_g, text="Y:").grid(row=1, column=2, sticky='e', padx=(1,1), pady=1)
        self.grid_y_entry = ttk.Entry(grid_g, width=7)
        self.grid_y_entry.insert(0, "5.0")
        self.grid_y_entry.grid(row=1, column=3, sticky='w', padx=0, pady=1)
        
        # 线形和线宽放在同一行
        ttk.Label(grid_g, text="线形:").grid(row=2, column=0, sticky='e', padx=(0,1), pady=1)
        self.grid_linestyle_var = tk.StringVar(value="虚线")
        self.grid_linestyle_combo = ttk.Combobox(grid_g, textvariable=self.grid_linestyle_var,
                                               values=["虚线", "实线", "点线", "点划线"],
                                               width=5, state="readonly")
        self.grid_linestyle_combo.grid(row=2, column=1, sticky='w', padx=0, pady=1)
        self.grid_linestyle_combo.bind('<<ComboboxSelected>>', self.on_grid_linestyle_change)
        
        ttk.Label(grid_g, text="宽:").grid(row=2, column=2, sticky='e', padx=(1,1), pady=1)
        self.grid_linewidth_var = tk.StringVar(value="0.5")
        self.grid_linewidth_combo = ttk.Combobox(grid_g, textvariable=self.grid_linewidth_var,
                                                values=["0.3", "0.5", "0.8", "1.0"],
                                                width=5, state="readonly")
        self.grid_linewidth_combo.grid(row=2, column=3, sticky='w', padx=0, pady=1)
        self.grid_linewidth_combo.bind('<<ComboboxSelected>>', self.on_grid_linewidth_change)
        
        # 颜色单独一行
        ttk.Label(grid_g, text="色:").grid(row=3, column=0, sticky='e', padx=(0,1), pady=1)
        self.grid_color_var = tk.StringVar(value="黑色")
        self.grid_color_combo = ttk.Combobox(grid_g, textvariable=self.grid_color_var,
                                           values=["黑色", "灰色", "蓝色", "红色", "绿色"],
                                           width=5, state="readonly")
        self.grid_color_combo.grid(row=3, column=1, sticky='w', padx=0, pady=1)
        self.grid_color_combo.bind('<<ComboboxSelected>>', self.on_grid_color_change)
        
        ttk.Button(grid_g, text="应用", width=10, 
                  command=self.apply_grid_interval).grid(row=4, column=0, columnspan=4, sticky='ew', padx=1, pady=1)
        
        grid_g.columnconfigure(0, weight=0)
        grid_g.columnconfigure(1, weight=0, minsize=0)  # 移除列1扩展以减小间距
        grid_g.columnconfigure(2, weight=0, minsize=1)  # 减小标签列宽度
        grid_g.columnconfigure(3, weight=0, minsize=0)  # 移除列3扩展以减小间距
        
        # 创建但不显示插入关键帧按钮
        self.insert_keyframe_btn = ttk.Button(self.scrollable_frame, text="插入关键帧", command=self.insert_keyframe, state='disabled')
        # 不调用pack()方法，按钮将不会显示在界面上

        # 批量插入关键帧按钮将在时间轴区域创建
        
        # 强制更新scrollable_frame和canvas的布局
        self.scrollable_frame.update_idletasks()
        
        # 确保输入框都已创建和显示
        print(f"✓ 文本框设置UI创建完成")
        print(f"  - 名称输入框: {self.textbox_name_entry.winfo_exists()}")
        print(f"  - 内容输入框: {self.textbox_content_entry.winfo_exists()}")
        
    def import_audio(self):
        """导入音频文件"""
        try:
            # 让用户选择音频文件
            file_path = filedialog.askopenfilename(
                filetypes=[
                    ("音频文件", "*.wav;*.mp3"),
                    ("WAV文件", "*.wav"),
                    ("MP3文件", "*.mp3"),
                    ("所有文件", "*.*")
                ],
                title="导入音频"
            )
            
            if not file_path:  # 用户取消选择
                return
            
            # 检查文件是否存在
            if not os.path.exists(file_path):
                messagebox.showerror("错误", f"文件不存在: {file_path}")
                return
                
            # 停止当前播放的音频
            if self.audio_file:
                pygame.mixer.music.stop()
                pygame.mixer.music.unload()  # 先卸载旧音频
            
            # 对于WAV文件，先检查格式是否支持
            if file_path.lower().endswith('.wav'):
                try:
                    with contextlib.closing(wave.open(file_path, 'r')) as f:
                        channels = f.getnchannels()
                        sample_width = f.getsampwidth()
                        framerate = f.getframerate()
                        print(f"📊 WAV文件格式: {framerate}Hz, {channels}声道, {sample_width*8}位")
                        
                        # 检查是否是常见的音频格式
                        if channels not in [1, 2]:
                            messagebox.showwarning("警告", 
                                f"不常见的声道数 ({channels})，可能存在兼容性问题")
                        
                        if sample_width not in [1, 2]:
                            messagebox.showwarning("警告", 
                                f"不常见的位深度 ({sample_width*8}位)，可能存在兼容性问题")
                        
                        if framerate < 8000 or framerate > 192000:
                            messagebox.showwarning("警告", 
                                f"不常见的采样率 ({framerate}Hz)，可能存在兼容性问题")
                            
                except Exception as e:
                    print(f"⚠️ 检查WAV格式时出错: {str(e)}")
                    # 继续尝试加载，即使检查失败
            
            # 加载新的音频文件
            try:
                pygame.mixer.music.load(file_path)
                self.audio_file = file_path
                
                # 重要：加载后立即设置音量（不使用sleep避免阻塞）
                pygame.mixer.music.set_volume(self.audio_volume)
                pygame.mixer.music.set_volume(self.audio_volume)  # 连续设置两次确保生效
                
                actual_vol = pygame.mixer.music.get_volume()
                print(f"✅ 音频文件加载成功: {os.path.basename(file_path)}")
                print(f"🔊 音频导入后音量: 设置={self.audio_volume:.2f}, 实际={actual_vol:.2f}")
            except pygame.error as e:
                error_msg = str(e)
                if "Unrecognized" in error_msg or "format" in error_msg.lower():
                    messagebox.showerror("音频格式不支持", 
                        f"无法加载该音频文件，可能是格式不支持。\n\n"
                        f"建议:\n"
                        f"1. 使用标准WAV格式 (44100Hz, 16位, 立体声)\n"
                        f"2. 使用MP3格式\n"
                        f"3. 使用音频转换工具转换格式\n\n"
                        f"错误详情: {error_msg}")
                else:
                    messagebox.showerror("音频加载失败", f"加载音频文件失败:\n{error_msg}")
                print(f"❌ 音频加载失败: {error_msg}")
                return
            except Exception as e:
                messagebox.showerror("错误", f"加载音频文件时发生错误:\n{str(e)}")
                print(f"❌ 音频加载失败: {str(e)}")
                return
            
            # 获取音频时长 - 使用多种方法尝试，确保可靠性
            duration_obtained = False
            
            # 方法1: 使用wave模块（适用于WAV文件）
            if file_path.lower().endswith('.wav') and not duration_obtained:
                try:
                    with contextlib.closing(wave.open(file_path, 'r')) as f:
                        frames = f.getnframes()
                        rate = f.getframerate()
                        if rate > 0 and frames > 0:
                            self.audio_duration = frames / float(rate)
                            print(f"⏱️ WAV音频时长(wave模块): {self.audio_duration:.2f}秒")
                            duration_obtained = True
                except Exception as e:
                    print(f"⚠️ wave模块获取时长失败: {str(e)}")
            
            # 方法2: 使用pygame.mixer.Sound（适用于所有格式）
            if not duration_obtained:
                try:
                    sound = pygame.mixer.Sound(file_path)
                    duration = sound.get_length()
                    if duration > 0:
                        self.audio_duration = duration
                        print(f"⏱️ 音频时长(pygame.Sound): {self.audio_duration:.2f}秒")
                        duration_obtained = True
                    del sound  # 释放资源
                except Exception as e:
                    print(f"⚠️ pygame.Sound获取时长失败: {str(e)}")
            
            # 方法3: 使用AudioFileClip（适用于MP3和其他格式）
            if not duration_obtained:
                try:
                    audio_clip = AudioFileClip(file_path)
                    if audio_clip.duration and audio_clip.duration > 0:
                        self.audio_duration = audio_clip.duration
                        print(f"⏱️ 音频时长(AudioFileClip): {self.audio_duration:.2f}秒")
                        duration_obtained = True
                    audio_clip.close()
                except Exception as e:
                    print(f"⚠️ AudioFileClip获取时长失败: {str(e)}")
            
            # 如果所有方法都失败，提示用户手动输入
            if not duration_obtained:
                print(f"❌ 无法自动获取音频时长")
                result = messagebox.askquestion("无法获取音频时长", 
                    "无法自动获取音频文件的时长。\n\n"
                    "是否要手动输入音频时长？\n"
                    "（如果选择'否'，将使用默认值60秒）")
                
                if result == 'yes':
                    # 弹出输入对话框
                    duration_dialog = tk.Toplevel(self.root)
                    duration_dialog.title("输入音频时长")
                    duration_dialog.geometry("300x150")
                    duration_dialog.transient(self.root)
                    duration_dialog.grab_set()
                    
                    ttk.Label(duration_dialog, text="请输入音频时长（秒）:", 
                             font=('Arial', 10)).pack(pady=20)
                    
                    duration_entry = ttk.Entry(duration_dialog, width=20, font=('Arial', 12))
                    duration_entry.pack(pady=10)
                    duration_entry.insert(0, "60")
                    duration_entry.focus()
                    
                    def confirm_duration():
                        try:
                            entered_duration = float(duration_entry.get())
                            if entered_duration > 0:
                                self.audio_duration = entered_duration
                                duration_dialog.destroy()
                            else:
                                messagebox.showerror("错误", "时长必须大于0")
                        except ValueError:
                            messagebox.showerror("错误", "请输入有效的数字")
                    
                    ttk.Button(duration_dialog, text="确定", 
                              command=confirm_duration).pack(pady=10)
                    
                    duration_dialog.wait_window()
                else:
                    self.audio_duration = 60  # 默认60秒
                    print(f"⚠️ 使用默认时长: 60秒")
            
            # 更新时间轴总秒数
            self.total_seconds = self.audio_duration
            self.total_frames = int(self.total_seconds * self.fps)
            
            # 更新UI显示
            self.seconds_entry.delete(0, tk.END)
            self.seconds_entry.insert(0, str(self.total_seconds))
            
            # 更新时间轴滑块
            self.time_scale.config(to=self.total_seconds)
            
            # 更新演员位置数组
            for actor in self.actors:
                old_positions = actor["positions"]
                actor["positions"] = [old_positions[0] for _ in range(self.total_frames)]  # 使用初始位置填充
                for i in range(min(len(old_positions), self.total_frames)):
                    actor["positions"][i] = old_positions[i]
                # 清理超出范围的关键帧
                actor["keyframes"] = [frame for frame in actor["keyframes"] if frame < self.total_frames]
                # 更新中间帧插值
                if len(actor["keyframes"]) >= 2:
                    self.update_intermediate_frames(actor)
                # 更新旋转数组
                if "rotations" in actor:
                    old_rotations = actor["rotations"]
                    actor["rotations"] = [0.0 for _ in range(self.total_frames)]
                    for i in range(min(len(old_rotations), self.total_frames)):
                        actor["rotations"][i] = old_rotations[i]
                else:
                    actor["rotations"] = [0.0 for _ in range(self.total_frames)]
                # 清理超出范围的旋转关键帧
                if "rotation_keyframes" in actor:
                    actor["rotation_keyframes"] = [frame for frame in actor["rotation_keyframes"] if frame < self.total_frames]
                    # 更新旋转插值
                    if len(actor["rotation_keyframes"]) >= 2:
                        self.update_intermediate_rotations(actor)
                else:
                    actor["rotation_keyframes"] = []
            
            # 更新道具位置数组
            for prop in self.props:
                old_positions = prop["positions"]
                prop["positions"] = [old_positions[0] for _ in range(self.total_frames)]  # 使用初始位置填充
                for i in range(min(len(old_positions), self.total_frames)):
                    prop["positions"][i] = old_positions[i]
                # 清理超出范围的关键帧
                prop["keyframes"] = [frame for frame in prop["keyframes"] if frame < self.total_frames]
                # 更新中间帧插值
                if len(prop["keyframes"]) >= 2:
                    self.update_intermediate_frames(prop)
                # 更新旋转数组
                if "rotations" in prop:
                    old_rotations = prop["rotations"]
                    prop["rotations"] = [0.0 for _ in range(self.total_frames)]
                    for i in range(min(len(old_rotations), self.total_frames)):
                        prop["rotations"][i] = old_rotations[i]
                else:
                    prop["rotations"] = [0.0 for _ in range(self.total_frames)]
                # 清理超出范围的旋转关键帧
                if "rotation_keyframes" in prop:
                    prop["rotation_keyframes"] = [frame for frame in prop["rotation_keyframes"] if frame < self.total_frames]
                    # 更新旋转插值
                    if len(prop["rotation_keyframes"]) >= 2:
                        self.update_intermediate_rotations(prop)
                else:
                    prop["rotation_keyframes"] = []
            
            # 更新旧版文本框内容数组
            old_contents = self.text_box["contents"]
            self.text_box["contents"] = ["" for _ in range(self.total_frames)]
            for i in range(min(len(old_contents), self.total_frames)):
                self.text_box["contents"][i] = old_contents[i]
            
            # 更新新版文本框系统
            for textbox in self.textboxes:
                # 更新位置数组
                if "positions" in textbox:
                    old_positions = textbox["positions"]
                    textbox["positions"] = [textbox["positions"][0] if textbox["positions"] else (0, 0) for _ in range(self.total_frames)]
                    for i in range(min(len(old_positions), self.total_frames)):
                        textbox["positions"][i] = old_positions[i]
                
                # 更新内容数组（保留现有内容）
                if "contents" in textbox:
                    old_contents = textbox["contents"]
                    textbox["contents"] = ["" for _ in range(self.total_frames)]
                    for i in range(min(len(old_contents), self.total_frames)):
                        textbox["contents"][i] = old_contents[i]
                
                # 更新样式数组（保留现有样式）
                if "char_styles_per_frame" in textbox:
                    old_styles = textbox["char_styles_per_frame"]
                    textbox["char_styles_per_frame"] = [[] for _ in range(self.total_frames)]
                    for i in range(min(len(old_styles), self.total_frames)):
                        textbox["char_styles_per_frame"][i] = old_styles[i]
                
                # 清理超出范围的关键帧
                if "keyframes" in textbox:
                    textbox["keyframes"] = [frame for frame in textbox["keyframes"] if frame < self.total_frames]
                    # 如果需要，更新中间帧插值
                    if len(textbox["keyframes"]) >= 2:
                        self.update_intermediate_frames(textbox)
            
            # 重置当前帧和时间
            self.current_frame = 0
            self.current_second = 0
            
            # 停止任何正在进行的动画
            if hasattr(self, 'animation_loop') and self.animation_loop.running:
                self.animation_loop.stop()
            
            # 重置拖动状态
            self.dragging = False
            self.drag_item = None
            self.drag_type = None
            self.drag_index = None
            self.drag_start_pos = None
            self.drag_end_pos = None
            
            # 重置时间轴滑块标志
            self.is_time_scale_updating = False
            
            # 更新时间轴滑块位置
            self.time_scale.set(0)
            
            # 更新显示
            self.update_stage_preview()
            
            # 强制更新画布
            self.canvas.draw()
            
            # 最终确认音量设置（不使用sleep避免阻塞）
            pygame.mixer.music.set_volume(self.audio_volume)
            pygame.mixer.music.set_volume(self.audio_volume)
            pygame.mixer.music.set_volume(self.audio_volume)
            
            actual_volume = pygame.mixer.music.get_volume()
            print(f"✅ 音频导入完成，最终音量: {actual_volume:.2f} (目标: {self.audio_volume:.2f})")
            
            # 显示成功消息
            self.log(f"✓ 音频已导入，时长: {self.audio_duration:.2f}秒", 'success')
            
            # 启用删除音频按钮
            if hasattr(self, 'remove_audio_btn'):
                self.remove_audio_btn.config(state='normal')
            
        except Exception as e:
            error_msg = f"导入音频失败: {str(e)}"
            print(error_msg)  # 打印详细错误信息
            messagebox.showerror("错误", error_msg)

    def play_audio(self):
        """播放音频"""
        if self.audio_file:
            pygame.mixer.music.play(loops=0, start=self.current_second)

    def pause_audio(self):
        """暂停音频"""
        if self.audio_file:
            pygame.mixer.music.pause()

    def stop_audio(self):
        """停止音频"""
        if self.audio_file:
            pygame.mixer.music.stop()
            self.current_second = 0
            self.current_frame = 0
            self.time_scale.set(0)
            self.update_stage_preview()

    def remove_audio(self):
        """删除导入的音频文件"""
        if not self.audio_file:
            self.log("⚠️ 当前没有导入的音频文件", 'warning')
            return
        
        # 确认删除
        result = messagebox.askyesno("确认删除", 
                                       f"确定要删除音频文件吗？\n\n文件: {os.path.basename(self.audio_file)}\n\n注意：删除后将无法使用带音频导出功能。")
        
        if not result:
            return
        
        try:
            # 停止当前播放的音频
            if self.audio_file:
                pygame.mixer.music.stop()
            
            # 停止任何正在进行的动画
            if hasattr(self, 'animation_loop') and self.animation_loop.running:
                self.animation_loop.stop()
            
            # 清除音频文件引用
            old_audio_file = self.audio_file
            self.audio_file = None
            self.audio_duration = 0
            
            # 重置当前帧和时间到开始位置
            self.current_frame = 0
            self.current_second = 0
            
            # 重置拖动状态
            self.dragging = False
            self.drag_item = None
            self.drag_type = None
            self.drag_index = None
            self.drag_start_pos = None
            self.drag_end_pos = None
            
            # 重置时间轴滑块标志
            self.is_time_scale_updating = False
            
            # 更新时间轴滑块位置到开始
            self.time_scale.set(0)
            
            # 更新显示
            self.update_stage_preview()
            
            # 强制更新画布
            self.canvas.draw()
            
            # 显示成功消息
            self.log(f"✓ 音频文件已删除: {os.path.basename(old_audio_file)}", 'success')
            
            # 禁用删除音频按钮
            if hasattr(self, 'remove_audio_btn'):
                self.remove_audio_btn.config(state='disabled')
            
        except Exception as e:
            error_msg = f"删除音频失败: {str(e)}"
            print(error_msg)  # 打印详细错误信息
            messagebox.showerror("错误", error_msg)

    def create_stage_preview(self):
        # 创建中间区域的容器
        center_frame = ttk.Frame(self.main_frame)
        center_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # 创建舞台预览
        preview_frame = ttk.LabelFrame(center_frame, text="舞台预览")
        preview_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 5))
        
        # 创建matplotlib图形 - 不固定大小，让它自适应容器
        self.fig = Figure()
        self.ax = self.fig.add_subplot(111)
        self.canvas = FigureCanvasTkAgg(self.fig, master=preview_frame)
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
        # 设置图形布局参数（使用 subplots_adjust 而不是 tight_layout，避免窗口移动）
        # left, bottom, right, top 分别表示子图区域的边界（0-1之间的比例）
        self.fig.subplots_adjust(left=0.08, bottom=0.08, right=0.95, top=0.95)
        
        # 初始化舞台显示
        self.update_stage_preview()
        
        # 添加鼠标事件处理
        self.canvas.mpl_connect('button_press_event', self.on_mouse_press)
        self.canvas.mpl_connect('button_release_event', self.on_mouse_release)
        self.canvas.mpl_connect('motion_notify_event', self.on_mouse_move)
        self.canvas.mpl_connect('scroll_event', self.on_mouse_scroll)  # 添加滚轮事件
        
        # 添加键盘事件处理
        self.canvas.mpl_connect('key_press_event', self.on_key_press)
        
        # 创建时间轴区域 - 在舞台预览下方
        timeline_frame = ttk.LabelFrame(center_frame, text="时间轴")
        timeline_frame.pack(fill=tk.X, pady=(5, 0))
        
        # 添加自定义标尺控制区域
        snap_frame = ttk.Frame(timeline_frame)
        snap_frame.pack(fill=tk.X, padx=5, pady=2)
        
        # 滑块吸附间隔输入
        ttk.Label(snap_frame, text="滑块吸附间隔(秒):").pack(side=tk.LEFT, padx=2)
        self.snap_interval_entry = ttk.Entry(snap_frame, width=5)
        self.snap_interval_entry.pack(side=tk.LEFT, padx=2)
        self.snap_interval_entry.insert(0, "1.0")  # 默认1.0秒（小数点后1位）
        # 使用FocusOut和Return事件，而不是KeyRelease，允许用户完整输入
        self.snap_interval_entry.bind('<FocusOut>', self.on_snap_interval_change)
        self.snap_interval_entry.bind('<Return>', self.on_snap_interval_change)
        
        # 自定义标尺间隔输入
        ttk.Label(snap_frame, text="自定义标尺间隔(秒):").pack(side=tk.LEFT, padx=(20, 2))
        self.custom_interval_entry = ttk.Entry(snap_frame, width=5)
        self.custom_interval_entry.pack(side=tk.LEFT, padx=2)
        self.custom_interval_entry.insert(0, "5")  # 默认5秒
        self.custom_interval_entry.bind('<KeyRelease>', self.on_custom_interval_change)
        
        # 标尺开关按钮
        self.ruler_enabled = tk.BooleanVar(value=False)
        ruler_checkbox = ttk.Checkbutton(snap_frame, text="显示标尺", 
                                       variable=self.ruler_enabled,
                                       command=self.on_ruler_toggle)
        ruler_checkbox.pack(side=tk.LEFT, padx=10)
        
        # 批量插入关键帧按钮
        self.batch_insert_keyframe_btn = ttk.Button(snap_frame, text="批量插入关键帧", command=self.batch_insert_keyframe)
        self.batch_insert_keyframe_btn.pack(side=tk.LEFT, padx=10)
        
        # 对齐功能菜单按钮
        self.align_menu_btn = ttk.Menubutton(snap_frame, text="对齐 ▼")
        self.align_menu_btn.pack(side=tk.LEFT, padx=5)
        
        # 创建对齐菜单
        align_menu = tk.Menu(self.align_menu_btn, tearoff=0)
        self.align_menu_btn.config(menu=align_menu)
        
        # 添加对齐选项
        align_menu.add_command(label="对齐到舞台中心", command=lambda: self.quick_align("center"))
        align_menu.add_command(label="左对齐", command=lambda: self.quick_align("left"))
        align_menu.add_command(label="右对齐", command=lambda: self.quick_align("right"))
        align_menu.add_command(label="上对齐", command=lambda: self.quick_align("top"))
        align_menu.add_command(label="下对齐", command=lambda: self.quick_align("bottom"))
        
        # 自由对齐模式开关（智能吸附）
        self.smart_align_enabled = tk.BooleanVar(value=False)
        self.smart_align_checkbox = ttk.Checkbutton(snap_frame, text="智能吸附", 
                                                    variable=self.smart_align_enabled)
        self.smart_align_checkbox.pack(side=tk.LEFT, padx=5)
        
        # 标尺显示容器 - 使用可滚动Canvas
        self.ruler_container = ttk.Frame(timeline_frame)
        # 默认不显示，只有在启用标尺时才显示
        
        # 创建Canvas用于横向滚动
        self.ruler_canvas = tk.Canvas(self.ruler_container, height=40, bg='white')
        self.ruler_scrollbar = ttk.Scrollbar(self.ruler_container, orient=tk.HORIZONTAL, command=self.ruler_canvas.xview)
        self.ruler_frame = ttk.Frame(self.ruler_canvas)
        
        # 配置Canvas
        self.ruler_canvas.configure(xscrollcommand=self.ruler_scrollbar.set)
        self.ruler_canvas.create_window((0, 0), window=self.ruler_frame, anchor='nw')
        
        # 绑定配置事件
        self.ruler_frame.bind('<Configure>', lambda e: self.ruler_canvas.configure(scrollregion=self.ruler_canvas.bbox('all')))
        
        # 布局（仅在显示标尺时pack）
        self.ruler_canvas.pack(side=tk.TOP, fill=tk.X, expand=False)
        self.ruler_scrollbar.pack(side=tk.TOP, fill=tk.X)
        
        # 时间轴滑块 - 使用tk.Scale替代ttk.Scale
        self.time_scale = tk.Scale(timeline_frame, 
                                 from_=0, 
                                 to=self.total_seconds,  # 修复：允许到达总秒数
                                 orient=tk.HORIZONTAL,
                                 command=self.on_time_scale_change,
                                 resolution=0.1,  # 设置分辨率为0.1秒，实现更平滑的播放
                                 showvalue=True,  # 显示当前值
                                 tickinterval=0)  # 设置刻度间隔为0，不显示刻度
        self.time_scale.pack(fill=tk.X, padx=5, pady=5)
        
        # 绑定鼠标事件以检测用户拖动
        self.time_scale.bind('<ButtonPress-1>', self.on_time_scale_press)
        self.time_scale.bind('<ButtonRelease-1>', self.on_time_scale_release)
        
        # 初始化标尺相关变量
        self.custom_interval = 5  # 默认自定义间隔5秒
        self.ruler_buttons = []  # 存储标尺按钮
        
        # 播放控制按钮
        control_frame = ttk.Frame(timeline_frame)
        control_frame.pack(fill=tk.X, padx=5, pady=5)
        
        # 创建播放控制按钮并绑定事件
        print("正在创建播放按钮...")  # 调试信息
        self.play_button = ttk.Button(control_frame, text="播放", command=self.play_animation)
        self.play_button.pack(side=tk.LEFT, padx=5)
        print("播放按钮创建完成")  # 调试信息
        
        print("正在创建暂停按钮...")  # 调试信息
        self.pause_button = ttk.Button(control_frame, text="暂停", command=self.pause_animation)
        self.pause_button.pack(side=tk.LEFT, padx=5)
        print("暂停按钮创建完成")  # 调试信息
        
        print("正在创建停止按钮...")  # 调试信息
        self.stop_button = ttk.Button(control_frame, text="停止", command=self.stop_animation)
        self.stop_button.pack(side=tk.LEFT, padx=5)
        print("停止按钮创建完成")  # 调试信息
        
        # 创建切换时间控件组
        switch_frame = ttk.Frame(control_frame)
        switch_frame.pack(side=tk.LEFT, padx=5)
        ttk.Label(switch_frame, text="切换时间(秒):").pack(side=tk.LEFT, padx=2)
        self.frame_switch_entry = ttk.Entry(switch_frame, width=8)
        self.frame_switch_entry.pack(side=tk.LEFT, padx=2)
        ttk.Button(switch_frame, text="切换", command=self.switch_frame).pack(side=tk.LEFT, padx=2)
        
        # 创建音量控制区域
        volume_frame = ttk.Frame(control_frame)
        volume_frame.pack(side=tk.RIGHT, padx=5)
        ttk.Label(volume_frame, text="音量:").pack(side=tk.LEFT, padx=2)
        self.volume_scale = ttk.Scale(volume_frame, 
                                    from_=0, 
                                    to=100,
                                    orient=tk.HORIZONTAL,
                                    value=50,  # 默认音量50%
                                    length=100,  # 设置滑块长度
                                    command=self.on_volume_change)
        self.volume_scale.pack(side=tk.LEFT, padx=2)
        
    def create_timeline(self):
        # 创建右侧面板，设置固定宽度避免跳动（优化：减小宽度）
        right_frame = ttk.Frame(self.main_frame, width=390)
        right_frame.pack(side=tk.RIGHT, fill=tk.Y, padx=5, pady=5)
        right_frame.pack_propagate(False)  # 禁止子组件改变父容器大小
        
        # 创建关键帧编辑区域，限制最大高度
        keyframe_frame = ttk.LabelFrame(right_frame, text="关键帧编辑")
        keyframe_frame.pack(fill=tk.BOTH, expand=True, pady=5)
        keyframe_frame.pack_propagate(True)  # 允许自适应，但受右侧面板限制
        
        # 创建左侧列表（优化：减小宽度，增加高度）
        list_frame = ttk.Frame(keyframe_frame)
        list_frame.pack(side=tk.LEFT, fill=tk.Y, padx=5, pady=5)
        
        ttk.Label(list_frame, text="对象列表").pack()
        
        # 创建列表框（优化：减小宽度，增加高度）
        # 设置为 EXTENDED 模式支持批量选择（按住 Ctrl 或 Shift 多选）
        self.keyframe_listbox = tk.Listbox(list_frame, width=14, height=15, selectmode=tk.EXTENDED)
        self.keyframe_listbox.pack(fill=tk.Y, expand=True)
        
        # 创建右侧编辑区域
        self.edit_frame = ttk.Frame(keyframe_frame)
        self.edit_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # 当前选中项信息
        self.current_item_label = ttk.Label(self.edit_frame, text="请选择要编辑的演员或道具")
        self.current_item_label.pack(pady=5)
        
        # 创建关键帧表格（优化：增加高度，调整列宽）
        columns = ('时间点', 'X坐标', 'Y坐标')
        self.keyframe_tree = ttk.Treeview(self.edit_frame, columns=columns, show='headings', height=15)
        
        # 设置列标题（优化：调整列宽以适应更窄的面板）
        for col in columns:
            self.keyframe_tree.heading(col, text=col)
            self.keyframe_tree.column(col, width=70)
            
        self.keyframe_tree.pack(fill=tk.BOTH, expand=True, pady=5)
        
        # 添加滚动条
        scrollbar = ttk.Scrollbar(self.edit_frame, orient=tk.VERTICAL, command=self.keyframe_tree.yview)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.keyframe_tree.configure(yscrollcommand=scrollbar.set)
        
        # 绑定双击事件用于编辑关键帧
        self.keyframe_tree.bind('<Double-Button-1>', self.on_keyframe_double_click)
        
        # 添加按钮
        button_frame = ttk.Frame(self.edit_frame)
        button_frame.pack(fill=tk.X, pady=5)
        
        ttk.Button(button_frame, text="添加关键帧", command=self.add_keyframe).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="删除关键帧", command=self.delete_keyframe).pack(side=tk.LEFT, padx=5)
        
        # 旋转角度设置
        rotation_frame = ttk.Frame(self.edit_frame)
        rotation_frame.pack(fill=tk.X, pady=5, padx=5)
        
        ttk.Label(rotation_frame, text="旋转角度:").pack(side=tk.LEFT, padx=2)
        self.rotation_angle_entry = ttk.Entry(rotation_frame, width=8)
        self.rotation_angle_entry.insert(0, "0")
        self.rotation_angle_entry.pack(side=tk.LEFT, padx=2)
        ttk.Label(rotation_frame, text="度").pack(side=tk.LEFT, padx=2)
        ttk.Button(rotation_frame, text="设置旋转关键帧", command=self.set_rotation_keyframe).pack(side=tk.LEFT, padx=5)
        
        # 重置操作按钮行
        reset_frame = ttk.Frame(self.edit_frame)
        reset_frame.pack(fill=tk.X, pady=2)
        
        ttk.Button(reset_frame, text="重置到等候区", command=self.reset_to_waiting_area).pack(side=tk.LEFT, padx=5)
        ttk.Button(reset_frame, text="全部重置", command=self.reset_all_to_waiting_area).pack(side=tk.LEFT, padx=5)
        
        # 绑定事件
        self.keyframe_listbox.bind('<<ListboxSelect>>', self.on_keyframe_list_select)
        
        # 项目操作区域 - 移到原来作者信息的位置
        project_frame = ttk.LabelFrame(right_frame, text="项目操作")
        project_frame.pack(fill=tk.X, pady=5)
        
        # 将所有项目操作按钮放在同一行
        project_row = ttk.Frame(project_frame)
        project_row.pack(fill=tk.X, padx=5, pady=3)
        
        self.save_btn = ttk.Button(project_row, text="保存项目", command=self.save_project)
        self.save_btn.pack(side=tk.LEFT, padx=2)
        
        self.load_btn = ttk.Button(project_row, text="导入项目", command=self.load_project)
        self.load_btn.pack(side=tk.LEFT, padx=2)
        
        self.audio_btn = ttk.Button(project_row, text="导入音频", command=self.import_audio)
        self.audio_btn.pack(side=tk.LEFT, padx=2)
        
        self.remove_audio_btn = ttk.Button(project_row, text="删除音频", command=self.remove_audio)
        self.remove_audio_btn.pack(side=tk.LEFT, padx=2)
        
        # 初始状态：如果没有音频文件，禁用删除按钮
        if not hasattr(self, 'audio_file') or not self.audio_file:
            self.remove_audio_btn.config(state='disabled')
        
        # 导出操作区域（合并导出设置与导出操作）
        export_frame = ttk.LabelFrame(right_frame, text="导出设置与操作")
        export_frame.pack(fill=tk.X, padx=5, pady=5)
        
        # 导出帧率设置行
        fps_row = ttk.Frame(export_frame)
        fps_row.pack(fill=tk.X, padx=5, pady=(5, 3))
        
        ttk.Label(fps_row, text="导出帧率:").pack(side=tk.LEFT, padx=2)
        self.export_fps_entry = ttk.Entry(fps_row, width=8)
        self.export_fps_entry.insert(0, "10")  # 默认导出帧率
        self.export_fps_entry.pack(side=tk.LEFT, padx=2)
        ttk.Label(fps_row, text="FPS", foreground='gray').pack(side=tk.LEFT, padx=2)
        
        # 导出操作按钮行
        export_row = ttk.Frame(export_frame)
        export_row.pack(fill=tk.X, padx=5, pady=(3, 5))
        
        self.export_btn = ttk.Button(export_row, text="导出GIF动画", command=self.export_animation)
        self.export_btn.pack(side=tk.LEFT, padx=2)
        
        self.export_with_audio_btn = ttk.Button(export_row, text="导出带音频MP4", command=self.export_animation_with_audio)
        self.export_with_audio_btn.pack(side=tk.LEFT, padx=2)
        
        # 创建日志输出窗口 - 在软件信息上方，固定高度（优化：减小高度）
        log_frame = ttk.LabelFrame(right_frame, text="操作日志", height=140)
        log_frame.pack(fill=tk.X, pady=5)
        log_frame.pack_propagate(False)  # 禁止子组件改变容器大小
        
        # 创建Text组件用于显示日志，设置固定高度（优化：减少行数）
        self.log_text = tk.Text(log_frame, height=7, width=45,  # 减少到7行
                               font=('Consolas', 9),
                               bg='#2b2b2b', fg='#cccccc',
                               wrap=tk.WORD, state='disabled',
                               relief=tk.FLAT, borderwidth=0)
        self.log_text.pack(fill=tk.BOTH, expand=True, padx=2, pady=2)
        
        # 添加滚动条
        log_scrollbar = ttk.Scrollbar(self.log_text, orient=tk.VERTICAL, 
                                      command=self.log_text.yview)
        log_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.log_text.configure(yscrollcommand=log_scrollbar.set)
        
        # 配置文本标签样式
        self.log_text.tag_config('info', foreground='#7ec699')  # 绿色 - 普通信息
        self.log_text.tag_config('success', foreground='#5cb85c')  # 深绿 - 成功
        self.log_text.tag_config('warning', foreground='#f0ad4e')  # 橙色 - 警告
        self.log_text.tag_config('error', foreground='#d9534f')  # 红色 - 错误
        self.log_text.tag_config('undo', foreground='#5bc0de')  # 蓝色 - 撤销/重做
        
        # 创建作者信息区域 - 移到时间轴下面
        author_frame = ttk.LabelFrame(right_frame, text="软件信息")
        author_frame.pack(fill=tk.X, pady=5)
        
        # 作者信息文本
        author_info = """舞台走位动画制作工具 v2.8
由@天云 免费制作及分享
如有bug或好的优化建议，可联系：
QQ：1248360754 小红书：5615193523"""
        
        author_label = tk.Label(author_frame, text=author_info, 
                               justify='left', 
                               font=('Microsoft YaHei', 9),
                               fg='#333333',
                               bg='#f0f0f0',
                               padx=10, pady=8)
        author_label.pack(fill=tk.X, padx=5, pady=5)
        
        # 为所有按钮绑定空格键，调用我们的切换函数而不是按钮的默认行为
        # 使用lambda包装以防止事件传播到按钮的默认处理器
        def button_space_handler(e):
            self.toggle_play_pause(e)
            return "break"  # 阻止按钮的默认空格键行为
        
        self.root.bind_class("TButton", "<space>", button_space_handler)
        
        # 为非按钮区域也绑定空格键
        self.root.bind_all('<space>', self.toggle_play_pause)
        print("空格键已绑定到播放/暂停切换功能")

    def update_scale_labels(self):
        """更新时间轴刻度标签"""
        # 当前使用的tk.Scale本身有刻度显示功能，无需单独的刻度标签
        pass

    def on_keyframe_list_select(self, event):
        """处理关键帧列表选择事件（支持批量选择）"""
        selected_indices = self.keyframe_listbox.curselection()
        if not selected_indices:
            return
        
        actor_count = len(self.actors)
        prop_count = len(self.props)
        
        # 清空当前选择
        self.selected_items.clear()
        
        # 处理所有选中的项
        selected_objects = []
        first_item = None
        first_item_type = None
        
        for index in selected_indices:
            # 判断选中的是什么类型
            item_type = None
            item_index = None
            current_item = None
            
            if index < actor_count:
                current_item = self.actors[index]
                item_type = 'actor'
                item_index = index
            elif index < actor_count + prop_count:
                current_item = self.props[index - actor_count]
                item_type = 'prop'
                item_index = index - actor_count
            elif index < actor_count + prop_count + len(self.textboxes):
                current_item = self.textboxes[index - actor_count - prop_count]
                item_type = 'textbox'
                item_index = index - actor_count - prop_count
            else:
                # 向后兼容旧版文本框
                continue
            
            # 添加到选中列表
            if current_item is not None and item_type is not None:
                pos = self.get_item_current_position(current_item)
                self.selected_items.append({
                    'item': current_item,
                    'type': item_type,
                    'index': item_index,
                    'start_pos': pos
                })
                selected_objects.append({'item': current_item, 'type': item_type})
                
                # 记录第一个选中的对象（用于UI更新）
                if first_item is None:
                    first_item = current_item
                    first_item_type = item_type
        
        # 更新UI标签显示
        if len(selected_objects) == 1 and first_item is not None and first_item_type is not None:
            # 单选：显示对象详情
            item = first_item
            item_type = first_item_type
            self.current_item_label.config(text=f"当前编辑: {item_type} {item['name']}")
            
            # 更新输入框
            if item_type == 'actor':
                self.actor_name_entry.delete(0, tk.END)
                self.actor_name_entry.insert(0, item['name'])
            elif item_type == 'prop':
                self.prop_name_entry.delete(0, tk.END)
                self.prop_name_entry.insert(0, item['name'])
            elif item_type == 'textbox':
                self.textbox_name_entry.delete(0, tk.END)
                self.textbox_name_entry.insert(0, item.get('name', ''))
                
                # 显示当前帧的内容
                contents_array = item.get("contents", [])
                if self.current_frame < len(contents_array):
                    current_frame_content = contents_array[self.current_frame]
                else:
                    current_frame_content = ""
                
                self.textbox_content_entry.delete("1.0", tk.END)
                self.textbox_content_entry.insert("1.0", current_frame_content)
                
                # 更新样式信息
                styles = item.get("styles", {})
                if self.current_frame in styles:
                    style = styles[self.current_frame]
                    if "font_size" in style:
                        self.textbox_font_size.delete(0, tk.END)
                        self.textbox_font_size.insert(0, str(style["font_size"]))
                    if "color" in style:
                        self.textbox_color_var.set(style["color"])
                
                print(f"左侧文本框编辑区域已更新，名称：{item.get('name', '')}, 当前帧内容：{current_frame_content}")
            
            # 单选日志输出
            print(f"📋 从列表选中: {item['name']} ({item_type})")
        elif len(selected_objects) > 1:
            # 多选：显示选中数量
            names = ', '.join([obj['item']['name'] for obj in selected_objects])
            self.current_item_label.config(text=f"已选中 {len(selected_objects)} 个对象")
            print(f"📋 从列表批量选中: {len(selected_objects)} 个对象")
            self.log(f"🔘 已选中 {len(selected_objects)} 个对象: {names}", 'info')
        
        # 更新舞台预览以显示选中高亮
        self.update_stage_preview()
        
        # 清空关键帧表格
        for row in self.keyframe_tree.get_children():
            self.keyframe_tree.delete(row)
        
        # 只有单选时才显示关键帧数据
        if len(selected_objects) == 1 and first_item is not None:
            # 添加关键帧数据
            for frame in sorted(first_item["keyframes"]):
                pos = first_item["positions"][frame]
                seconds = frame / self.fps  # 使用除法，支持小数
                # 插入数据时，使用tags保存原始帧数，避免浮点数精度问题
                item_id = self.keyframe_tree.insert('', 'end', 
                                                    values=(f"{seconds:.1f}秒", f"{pos[0]:.1f}", f"{pos[1]:.1f}"))
                # 将原始帧数保存在item的tags中
                self.keyframe_tree.item(item_id, tags=(str(frame),))

    def update_keyframe_data(self):
        """更新关键帧数据"""
        selected = self.keyframe_listbox.curselection()
        if not selected:
            messagebox.showwarning("警告", "请先选择一个演员或道具")
            return
            
        index = selected[0]
        if index < len(self.actors):
            current_item = self.actors[index]
        else:
            current_item = self.props[index - len(self.actors)]
            
        try:
            # 获取所有行的值
            for item in self.keyframe_tree.get_children():
                values = self.keyframe_tree.item(item)['values']
                tags = self.keyframe_tree.item(item)['tags']
                
                # 从tags中获取原始帧数（避免浮点数精度问题）
                if tags and len(tags) > 0:
                    frame = int(tags[0])
                else:
                    # 兼容旧数据：如果没有tags，使用秒数计算
                    seconds = float(values[0].rstrip('秒'))
                    frame = int(seconds * self.fps)
                
                x = float(values[1])
                y = float(values[2])
                
                # 更新位置
                current_item["positions"][frame] = (x, y)
                
                # 确保时间点在关键帧列表中
                if frame not in current_item["keyframes"]:
                    current_item["keyframes"].append(frame)
                    current_item["keyframes"].sort()
                    
            # 更新中间帧
            self.update_intermediate_frames(current_item)
            
            # 更新舞台预览
            self.update_stage_preview()
            
            # 重新加载表格数据
            self.on_keyframe_list_select(None)
            
            # 显示成功提示
            messagebox.showinfo("成功", "关键帧数据已更新")
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))

    def add_keyframe(self):
        """添加关键帧"""
        selected = self.keyframe_listbox.curselection()
        if not selected:
            messagebox.showwarning("警告", "请先选择一个演员或道具")
            return
            
        index = selected[0]
        if index < len(self.actors):
            current_item = self.actors[index]
        else:
            current_item = self.props[index - len(self.actors)]
            
        try:
            # 保存当前选中状态（包括舞台上的选中）
            saved_selected_items = self.selected_items.copy()
            saved_listbox_selection = self.keyframe_listbox.curselection()
            
            # 创建新窗口
            add_dialog = tk.Toplevel(self.root)
            add_dialog.title("添加关键帧")
            
            # 设置对话框大小
            dialog_width = 250
            dialog_height = 170
            
            # 计算软件窗口的中心位置
            root_x = self.root.winfo_x()
            root_y = self.root.winfo_y()
            root_width = self.root.winfo_width()
            root_height = self.root.winfo_height()
            
            # 计算对话框应该显示的位置（软件窗口中心）
            x = root_x + (root_width - dialog_width) // 2
            y = root_y + (root_height - dialog_height) // 2
            
            add_dialog.geometry(f"{dialog_width}x{dialog_height}+{x}+{y}")
            add_dialog.transient(self.root)
            add_dialog.grab_set()
            
            # 添加输入框
            ttk.Label(add_dialog, text="时间点(秒):").grid(row=0, column=0, padx=5, pady=2)
            time_entry = ttk.Entry(add_dialog)
            time_entry.grid(row=0, column=1, padx=5, pady=2)
            
            ttk.Label(add_dialog, text="X坐标:").grid(row=1, column=0, padx=5, pady=2)
            x_entry = ttk.Entry(add_dialog)
            x_entry.grid(row=1, column=1, padx=5, pady=2)
            
            ttk.Label(add_dialog, text="Y坐标:").grid(row=2, column=0, padx=5, pady=2)
            y_entry = ttk.Entry(add_dialog)
            y_entry.grid(row=2, column=1, padx=5, pady=2)
            
            ttk.Label(add_dialog, text="旋转角度(度):").grid(row=3, column=0, padx=5, pady=2)
            rotation_entry = ttk.Entry(add_dialog)
            rotation_entry.insert(0, "0")
            rotation_entry.grid(row=3, column=1, padx=5, pady=2)
            
            def save_keyframe():
                try:
                    seconds = float(time_entry.get())  # 接受浮点数
                    # 四舍五入到小数点后1位
                    seconds = round(seconds, 1)
                    
                    if seconds < 0 or seconds >= self.total_seconds:
                        raise ValueError("时间点超出范围")
                        
                    frame = int(seconds * self.fps)  # 计算对应的帧数
                    x = float(x_entry.get())
                    y = float(y_entry.get())
                    rotation = float(rotation_entry.get())
                    
                    # 保存历史记录
                    self.save_state_to_history(f"添加关键帧 ({current_item['name']} @ {seconds}秒)")
                    
                    # 更新位置数据
                    current_item["positions"][frame] = (x, y)
                    if frame not in current_item["keyframes"]:
                        current_item["keyframes"].append(frame)
                        current_item["keyframes"].sort()
                        
                    # 更新旋转数据
                    if "rotations" not in current_item:
                        current_item["rotations"] = [0.0 for _ in range(self.total_frames)]
                    if "rotation_keyframes" not in current_item:
                        current_item["rotation_keyframes"] = []
                    
                    current_item["rotations"][frame] = rotation
                    if frame not in current_item["rotation_keyframes"]:
                        current_item["rotation_keyframes"].append(frame)
                        current_item["rotation_keyframes"].sort()
                        
                    # 更新中间帧插值
                    self.update_intermediate_frames(current_item)
                    self.update_intermediate_rotations(current_item)
                    
                    # 恢复列表框选择
                    if saved_listbox_selection:
                        self.keyframe_listbox.selection_clear(0, tk.END)
                        self.keyframe_listbox.selection_set(saved_listbox_selection[0])
                        self.keyframe_listbox.see(saved_listbox_selection[0])
                    
                    # 恢复舞台上的选中状态
                    self.selected_items = saved_selected_items.copy()
                    
                    # 刷新关键帧表格显示（在恢复选择后调用，确保表格正确更新）
                    self.on_keyframe_list_select(None)
                    
                    # 更新舞台预览以显示选中高亮
                    self.update_stage_preview()
                    
                    # 记录日志
                    self.log(f"✓ 添加关键帧: {current_item['name']} @ {seconds}秒", 'success')
                    
                    add_dialog.destroy()
                    
                except ValueError as e:
                    messagebox.showerror("错误", str(e))
                    
            def cancel_add():
                """取消添加，恢复选中状态"""
                # 恢复列表框选择
                if saved_listbox_selection:
                    self.keyframe_listbox.selection_clear(0, tk.END)
                    self.keyframe_listbox.selection_set(saved_listbox_selection[0])
                    self.keyframe_listbox.see(saved_listbox_selection[0])
                
                # 恢复舞台上的选中状态
                self.selected_items = saved_selected_items.copy()
                
                # 更新舞台预览以显示选中高亮
                self.update_stage_preview()
                
                add_dialog.destroy()
            
            ttk.Button(add_dialog, text="确定", command=save_keyframe).grid(row=4, column=0, columnspan=2, pady=10)
            
            # 焦点设置到时间输入框
            time_entry.focus()
            
            # 绑定回车键保存和Esc键取消
            add_dialog.bind('<Return>', lambda e: save_keyframe())
            add_dialog.bind('<Escape>', lambda e: cancel_add())
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))

    def set_rotation_keyframe(self):
        """为选中的演员/道具设置旋转角度关键帧"""
        if not self.selected_items:
            messagebox.showwarning("警告", "请先在舞台上选中一个演员或道具")
            return
        
        if len(self.selected_items) > 1:
            messagebox.showwarning("警告", "只能同时设置一个对象的旋转角度")
            return
        
        try:
            rotation = float(self.rotation_angle_entry.get())
            frame = self.current_frame
            
            # 保存历史记录
            item = self.selected_items[0]['item']
            self.save_state_to_history(f"设置旋转关键帧 ({item['name']} @ {self.current_second:.1f}秒)")
            
            # 确保存在旋转数组和关键帧列表
            if "rotations" not in item:
                item["rotations"] = [0.0 for _ in range(self.total_frames)]
            if "rotation_keyframes" not in item:
                item["rotation_keyframes"] = []
            
            # 设置旋转角度（不归一化，保留原始角度值以支持多圈旋转）
            item["rotations"][frame] = rotation
            
            # 添加关键帧
            if frame not in item["rotation_keyframes"]:
                item["rotation_keyframes"].append(frame)
                item["rotation_keyframes"].sort()
            
            # 更新旋转插值
            self.update_intermediate_rotations(item)
            
            # 更新显示
            self.update_stage_preview()
            
            # 记录日志
            self.log(f"✓ 设置旋转关键帧: {item['name']} @ {self.current_second:.1f}秒, 角度={rotation}°", 'success')
            
        except ValueError:
            messagebox.showerror("错误", "请输入有效的旋转角度（数字）")
    
    def quick_rotate(self, angle_delta):
        """快捷旋转选中的对象
        
        Args:
            angle_delta: 旋转角度增量（正数顺时针，负数逆时针）
        """
        if not self.selected_items:
            return
        
        # 过滤出演员和道具（不包括文本框）
        valid_items = [item for item in self.selected_items if item['type'] in ['actor', 'prop']]
        
        if not valid_items:
            return
        
        frame = self.current_frame
        
        # 保存历史记录
        if len(valid_items) == 1:
            self.save_state_to_history(f"旋转 ({valid_items[0]['item']['name']} {angle_delta:+.0f}°)")
        else:
            self.save_state_to_history(f"旋转 ({len(valid_items)}个对象 {angle_delta:+.0f}°)")
        
        for selected in valid_items:
            item = selected['item']
            
            # 确保存在旋转数组和关键帧列表
            if "rotations" not in item:
                item["rotations"] = [0.0 for _ in range(self.total_frames)]
            if "rotation_keyframes" not in item:
                item["rotation_keyframes"] = []
            
            # 获取当前旋转角度
            current_rotation = item["rotations"][frame]
            
            # 计算新旋转角度（不归一化，允许累积超过360度）
            new_rotation = current_rotation + angle_delta
            
            # 设置旋转角度
            item["rotations"][frame] = new_rotation
            
            # 添加关键帧
            if frame not in item["rotation_keyframes"]:
                item["rotation_keyframes"].append(frame)
                item["rotation_keyframes"].sort()
            
            # 更新旋转插值
            self.update_intermediate_rotations(item)
        
        # 更新显示
        self.update_stage_preview()
        
        # 更新UI输入框（如果只选中一个对象）
        if len(valid_items) == 1:
            new_rotation = valid_items[0]['item']["rotations"][frame]
            self.rotation_angle_entry.delete(0, tk.END)
            self.rotation_angle_entry.insert(0, f"{new_rotation:.1f}")
            
    def delete_keyframe(self):
        """删除关键帧（支持批量删除）"""
        # 首先检查是否在关键帧表格中选择了关键帧
        # 如果选择了，优先处理关键帧表格的选择（单个对象的多个关键帧）
        selected = self.keyframe_listbox.curselection()
        keyframes_selected = self.keyframe_tree.selection()
        
        print(f"🔍 delete_keyframe调用: 列表框选择={len(selected) if selected else 0}, 表格选择={len(keyframes_selected) if keyframes_selected else 0}, 多选对象={len(self.selected_items)}")
        
        if selected and keyframes_selected:
            # 从列表框选择对象，从表格选择关键帧
            index = selected[0]
            if index < len(self.actors):
                current_item = self.actors[index]
            else:
                current_item = self.props[index - len(self.actors)]
            
            # 检查是否选中了多个关键帧
            if len(keyframes_selected) > 1:
                # 批量删除单个对象的多个关键帧
                frames_to_delete = []
                time_points = []
                
                for keyframe_id in keyframes_selected:
                    # 从tags中获取原始帧数
                    tags = self.keyframe_tree.item(keyframe_id)['tags']
                    if tags and len(tags) > 0:
                        frame = int(tags[0])
                    else:
                        # 兼容旧数据
                        values = self.keyframe_tree.item(keyframe_id)['values']
                        seconds = float(values[0].rstrip('秒'))
                        frame = int(seconds * self.fps)
                    
                    frames_to_delete.append(frame)
                    time_points.append(f"{frame / self.fps:.1f}秒")
                
                # 确认删除
                time_list = ', '.join(time_points)
                if not messagebox.askyesno("确认", 
                    f"确定要删除 {current_item['name']} 的 {len(frames_to_delete)} 个关键帧吗？\n{time_list}"):
                    return
                
                # 保存历史记录
                self.save_state_to_history(f"批量删除关键帧 ({current_item['name']} {len(frames_to_delete)}个)")
                
                # 批量删除关键帧
                for frame in frames_to_delete:
                    if frame in current_item["keyframes"]:
                        current_item["keyframes"].remove(frame)
                
                # 更新中间帧插值
                self.update_intermediate_frames(current_item)
                
                # 更新显示
                self.on_keyframe_list_select(None)
                
                # 记录日志
                self.log(f"✓ 已删除 {current_item['name']} 的 {len(frames_to_delete)} 个关键帧", 'success')
                return
            elif len(keyframes_selected) == 1:
                # 单个删除模式
                tags = self.keyframe_tree.item(keyframes_selected[0])['tags']
                if tags and len(tags) > 0:
                    frame = int(tags[0])
                else:
                    values = self.keyframe_tree.item(keyframes_selected[0])['values']
                    seconds = float(values[0].rstrip('秒'))
                    frame = int(seconds * self.fps)
                
                seconds = frame / self.fps
                self.save_state_to_history(f"删除关键帧 ({current_item['name']} @ {seconds:.1f}秒)")
                
                if frame in current_item["keyframes"]:
                    current_item["keyframes"].remove(frame)
                else:
                    messagebox.showerror("错误", f"关键帧 {seconds:.1f}秒 不存在于列表中")
                    return
                
                self.update_intermediate_frames(current_item)
                self.on_keyframe_list_select(None)
                self.log(f"✓ 删除关键帧: {current_item['name']} @ {seconds}秒", 'success')
                return
        
        # 其次检查是否有多选对象（删除多个对象的当前帧关键帧）
        if len(self.selected_items) > 0:
            # 批量删除模式：删除所有选中对象在当前帧的关键帧
            print(f"🔍 进入多选对象删除模式，当前帧={self.current_frame}, 当前秒={self.current_second:.1f}")
            items_with_keyframe = []
            items_without_keyframe = []
            
            for selected_item in self.selected_items:
                obj = selected_item['item']
                print(f"   检查 {obj['name']}: 关键帧列表={obj['keyframes'][:5]}... (共{len(obj['keyframes'])}个)")
                if self.current_frame in obj["keyframes"]:
                    items_with_keyframe.append(obj)
                    print(f"   ✓ {obj['name']} 在当前帧有关键帧")
                else:
                    items_without_keyframe.append(obj)
                    print(f"   ✗ {obj['name']} 在当前帧无关键帧")
            
            if not items_with_keyframe:
                current_time = int(self.current_second)
                messagebox.showwarning("警告", f"所选对象在第 {current_time}秒 都没有关键帧")
                return
            
            # 确认删除
            names = ', '.join([item['name'] for item in items_with_keyframe])
            current_time = self.current_frame / self.fps
            if not messagebox.askyesno("确认", 
                f"确定要删除 {len(items_with_keyframe)} 个对象在 {current_time:.1f}秒 的关键帧吗？\n{names}"):
                return
            
            # 保存历史记录
            self.save_state_to_history(f"批量删除关键帧 ({len(items_with_keyframe)}个对象 @ {current_time:.1f}秒)")
            
            # 批量删除关键帧
            for obj in items_with_keyframe:
                obj["keyframes"].remove(self.current_frame)
                self.update_intermediate_frames(obj)
            
            # 更新显示（保持多选状态，不调用on_keyframe_list_select）
            self.update_stage_preview()
            
            # 显示结果
            if items_without_keyframe:
                self.log(f"✓ 已删除 {len(items_with_keyframe)} 个关键帧 ({len(items_without_keyframe)}个无关键帧)", 'success')
            else:
                self.log(f"✓ 已删除 {len(items_with_keyframe)} 个关键帧", 'success')
        else:
            # 从列表框选择对象模式
            selected = self.keyframe_listbox.curselection()
            if not selected:
                messagebox.showwarning("警告", "请先选择一个演员或道具")
                return
                
            index = selected[0]
            if index < len(self.actors):
                current_item = self.actors[index]
            else:
                current_item = self.props[index - len(self.actors)]
                
            keyframes_selected = self.keyframe_tree.selection()
            if not keyframes_selected:
                messagebox.showwarning("警告", "请先选择要删除的关键帧")
                return
            
            # 检查是否选中了多个关键帧
            if len(keyframes_selected) > 1:
                # 批量删除多个关键帧
                frames_to_delete = []
                time_points = []
                
                for keyframe_id in keyframes_selected:
                    # 从tags中获取原始帧数
                    tags = self.keyframe_tree.item(keyframe_id)['tags']
                    if tags and len(tags) > 0:
                        frame = int(tags[0])
                    else:
                        # 兼容旧数据
                        values = self.keyframe_tree.item(keyframe_id)['values']
                        seconds = float(values[0].rstrip('秒'))
                        frame = int(seconds * self.fps)
                    
                    frames_to_delete.append(frame)
                    time_points.append(f"{frame / self.fps:.1f}秒")
                
                # 确认删除
                time_list = ', '.join(time_points)
                if not messagebox.askyesno("确认", 
                    f"确定要删除 {current_item['name']} 的 {len(frames_to_delete)} 个关键帧吗？\n{time_list}"):
                    return
                
                # 保存历史记录
                self.save_state_to_history(f"批量删除关键帧 ({current_item['name']} {len(frames_to_delete)}个)")
                
                # 批量删除关键帧
                for frame in frames_to_delete:
                    if frame in current_item["keyframes"]:
                        current_item["keyframes"].remove(frame)
                
                # 更新中间帧插值
                self.update_intermediate_frames(current_item)
                
                # 更新显示
                self.on_keyframe_list_select(None)
                
                # 记录日志
                self.log(f"✓ 已删除 {current_item['name']} 的 {len(frames_to_delete)} 个关键帧", 'success')
            elif len(keyframes_selected) == 1:
                # 单个删除模式
                # 从tags中获取原始帧数（避免浮点数精度问题）
                tags = self.keyframe_tree.item(keyframes_selected[0])['tags']
                if tags and len(tags) > 0:
                    frame = int(tags[0])
                else:
                    # 兼容旧数据：如果没有tags，使用秒数计算
                    values = self.keyframe_tree.item(keyframes_selected[0])['values']
                    seconds = float(values[0].rstrip('秒'))
                    frame = int(seconds * self.fps)
                
                # 获取秒数用于显示
                seconds = frame / self.fps
                
                # 保存历史记录
                self.save_state_to_history(f"删除关键帧 ({current_item['name']} @ {seconds:.1f}秒)")
                
                # 删除关键帧（检查帧是否存在）
                if frame in current_item["keyframes"]:
                    current_item["keyframes"].remove(frame)
                else:
                    messagebox.showerror("错误", f"关键帧 {seconds:.1f}秒 不存在于列表中")
                    return
                
                # 更新中间帧插值
                self.update_intermediate_frames(current_item)
                
                # 更新显示
                self.on_keyframe_list_select(None)
                
                # 记录日志
                self.log(f"✓ 删除关键帧: {current_item['name']} @ {seconds}秒", 'success')
    
    def on_keyframe_double_click(self, event):
        """处理关键帧表格双击事件 - 编辑关键帧"""
        # 获取双击的行
        item_id = self.keyframe_tree.identify_row(event.y)
        if not item_id:
            return
        
        # 获取当前选中的对象
        selected = self.keyframe_listbox.curselection()
        if not selected:
            messagebox.showwarning("警告", "请先选择一个演员或道具")
            return
        
        index = selected[0]
        actor_count = len(self.actors)
        
        if index < actor_count:
            current_item = self.actors[index]
            item_type = 'actor'
            item_index = index
        elif index < actor_count + len(self.props):
            current_item = self.props[index - actor_count]
            item_type = 'prop'
            item_index = index - actor_count
        else:
            messagebox.showwarning("警告", "文本框暂不支持双击编辑关键帧")
            return
        
        # 保存当前选中状态（包括舞台上的选中）
        saved_selected_items = self.selected_items.copy()
        saved_listbox_selection = self.keyframe_listbox.curselection()
        
        # 获取关键帧数据
        tags = self.keyframe_tree.item(item_id)['tags']
        values = self.keyframe_tree.item(item_id)['values']
        
        if tags and len(tags) > 0:
            old_frame = int(tags[0])
        else:
            # 兼容旧数据
            seconds = float(values[0].rstrip('秒'))
            old_frame = int(seconds * self.fps)
        
        old_seconds = old_frame / self.fps
        old_x = float(values[1])
        old_y = float(values[2])
        
        # 获取旧的旋转角度
        old_rotation = 0.0
        if "rotations" in current_item and old_frame < len(current_item["rotations"]):
            old_rotation = current_item["rotations"][old_frame]
        
        # 创建编辑对话框
        edit_dialog = tk.Toplevel(self.root)
        edit_dialog.title(f"编辑关键帧 - {current_item['name']}")
        
        # 设置对话框大小
        dialog_width = 300
        dialog_height = 210
        
        # 计算软件窗口的中心位置
        root_x = self.root.winfo_x()
        root_y = self.root.winfo_y()
        root_width = self.root.winfo_width()
        root_height = self.root.winfo_height()
        
        # 计算对话框应该显示的位置（软件窗口中心）
        x = root_x + (root_width - dialog_width) // 2
        y = root_y + (root_height - dialog_height) // 2
        
        edit_dialog.geometry(f"{dialog_width}x{dialog_height}+{x}+{y}")
        edit_dialog.transient(self.root)
        edit_dialog.grab_set()
        
        # 时间点
        ttk.Label(edit_dialog, text="时间点(秒):").grid(row=0, column=0, padx=10, pady=10, sticky='e')
        time_entry = ttk.Entry(edit_dialog, width=15)
        time_entry.insert(0, f"{old_seconds:.1f}")
        time_entry.grid(row=0, column=1, padx=10, pady=10)
        
        # X坐标
        ttk.Label(edit_dialog, text="X坐标:").grid(row=1, column=0, padx=10, pady=10, sticky='e')
        x_entry = ttk.Entry(edit_dialog, width=15)
        x_entry.insert(0, f"{old_x:.1f}")
        x_entry.grid(row=1, column=1, padx=10, pady=10)
        
        # Y坐标
        ttk.Label(edit_dialog, text="Y坐标:").grid(row=2, column=0, padx=10, pady=10, sticky='e')
        y_entry = ttk.Entry(edit_dialog, width=15)
        y_entry.insert(0, f"{old_y:.1f}")
        y_entry.grid(row=2, column=1, padx=10, pady=10)
        
        # 旋转角度
        ttk.Label(edit_dialog, text="旋转角度(度):").grid(row=3, column=0, padx=10, pady=10, sticky='e')
        rotation_entry = ttk.Entry(edit_dialog, width=15)
        rotation_entry.insert(0, f"{old_rotation:.1f}")
        rotation_entry.grid(row=3, column=1, padx=10, pady=10)
        
        def save_changes():
            try:
                new_seconds = float(time_entry.get())
                new_seconds = round(new_seconds, 1)
                
                if new_seconds < 0 or new_seconds >= self.total_seconds:
                    raise ValueError("时间点超出范围")
                
                new_frame = int(new_seconds * self.fps)
                new_x = float(x_entry.get())
                new_y = float(y_entry.get())
                new_rotation = float(rotation_entry.get())
                
                # 保存历史记录
                self.save_state_to_history(f"编辑关键帧 ({current_item['name']} {old_seconds:.1f}秒→{new_seconds:.1f}秒)")
                
                # 如果时间点改变了
                if old_frame != new_frame:
                    # 删除旧关键帧
                    if old_frame in current_item["keyframes"]:
                        current_item["keyframes"].remove(old_frame)
                    
                    # 添加新关键帧
                    if new_frame not in current_item["keyframes"]:
                        current_item["keyframes"].append(new_frame)
                        current_item["keyframes"].sort()
                    
                    # 处理旋转关键帧
                    if "rotation_keyframes" in current_item:
                        if old_frame in current_item["rotation_keyframes"]:
                            current_item["rotation_keyframes"].remove(old_frame)
                        if new_frame not in current_item["rotation_keyframes"]:
                            current_item["rotation_keyframes"].append(new_frame)
                            current_item["rotation_keyframes"].sort()
                
                # 更新位置
                current_item["positions"][new_frame] = (new_x, new_y)
                
                # 更新旋转角度
                if "rotations" not in current_item:
                    current_item["rotations"] = [0.0 for _ in range(self.total_frames)]
                if "rotation_keyframes" not in current_item:
                    current_item["rotation_keyframes"] = []
                
                current_item["rotations"][new_frame] = new_rotation
                if new_frame not in current_item["rotation_keyframes"]:
                    current_item["rotation_keyframes"].append(new_frame)
                    current_item["rotation_keyframes"].sort()
                
                # 更新中间帧
                self.update_intermediate_frames(current_item)
                self.update_intermediate_rotations(current_item)
                
                # 恢复列表框选择
                if saved_listbox_selection:
                    self.keyframe_listbox.selection_clear(0, tk.END)
                    self.keyframe_listbox.selection_set(saved_listbox_selection[0])
                    self.keyframe_listbox.see(saved_listbox_selection[0])
                
                # 恢复舞台上的选中状态
                self.selected_items = saved_selected_items.copy()
                
                # 刷新关键帧表格显示（在恢复选择后调用，确保表格正确更新）
                self.on_keyframe_list_select(None)
                
                # 更新舞台预览以显示选中高亮
                self.update_stage_preview()
                
                # 记录日志
                if old_frame != new_frame:
                    self.log(f"✓ 关键帧已修改: {current_item['name']} {old_seconds:.1f}秒→{new_seconds:.1f}秒", 'success')
                else:
                    self.log(f"✓ 关键帧已修改: {current_item['name']} @ {new_seconds:.1f}秒", 'success')
                
                edit_dialog.destroy()
                
            except ValueError as e:
                messagebox.showerror("错误", f"输入数据无效: {str(e)}")
        
        def cancel_changes():
            """取消编辑，恢复选中状态"""
            # 恢复列表框选择
            if saved_listbox_selection:
                self.keyframe_listbox.selection_clear(0, tk.END)
                self.keyframe_listbox.selection_set(saved_listbox_selection[0])
                self.keyframe_listbox.see(saved_listbox_selection[0])
            
            # 恢复舞台上的选中状态
            self.selected_items = saved_selected_items.copy()
            
            # 更新舞台预览以显示选中高亮
            self.update_stage_preview()
            
            edit_dialog.destroy()
        
        # 按钮区域
        button_frame = ttk.Frame(edit_dialog)
        button_frame.grid(row=4, column=0, columnspan=2, pady=15)
        
        ttk.Button(button_frame, text="保存", command=save_changes, width=10).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="取消", command=cancel_changes, width=10).pack(side=tk.LEFT, padx=5)
        
        # 焦点设置到时间输入框
        time_entry.focus()
        time_entry.select_range(0, tk.END)
        
        # 绑定回车键保存和ESC键取消
        edit_dialog.bind('<Return>', lambda e: save_changes())
        edit_dialog.bind('<Escape>', lambda e: cancel_changes())
        
        print(f"📝 双击编辑关键帧: {current_item['name']} @ {old_seconds:.1f}秒")
        
    def update_stage_preview(self):
        self.ax.clear()
        
        # 首先关闭matplotlib默认网格，避免与自定义辅助线冲突
        self.ax.grid(False)
        
        # 确保所有文本框的数组都有效
        self.ensure_all_textboxes_valid()
        
        # 计算不可见区域宽度（所有情况下都需要）
        invisible_width = self.stage_width / 8  # 左右备台区域宽度为舞台宽度的1/8
        
        # 如果正在播放且有固定视图范围，使用固定范围
        min_y = 0

        if self.is_playing and self.fixed_view_range:
            xlim = self.fixed_view_range['xlim']
            ylim = self.fixed_view_range['ylim']
            # 直接使用捕获的固定范围，不要再次应用缩放
            # （捕获时已经包含了缩放和平移的效果）
            self.ax.set_xlim(xlim)
            self.ax.set_ylim(ylim)
            min_y = float(ylim[0])  # 保证min_y有值
            # 设置固定的长宽比
            self.ax.set_aspect('equal', adjustable='datalim')
        else:
            # 动态计算视图范围
            waiting_actors = self.get_waiting_area_actors()
            waiting_props = self.get_waiting_area_props()
            for actor in waiting_actors:
                for pos in actor["positions"]:
                    min_y = min(min_y, pos[1] - actor["size"])
            for prop in waiting_props:
                for pos in prop["positions"]:
                    min_y = min(min_y, pos[1] - max(prop["width"], prop["height"])/2)
            min_audience_height = self.calculate_minimum_audience_height()
            min_y = min(min_y, -min_audience_height)
            if waiting_actors or waiting_props or len(self.actors) > 0 or len(self.props) > 0:
                min_y -= 1.0
            
            # 计算基础视图范围
            base_x_min = -self.stage_width/2 - invisible_width
            base_x_max = self.stage_width/2 + invisible_width
            backstage_height = self.stage_height / 8
            base_y_min = min_y
            base_y_max = self.stage_height + backstage_height + 1
            
            # 当用户进行了缩放或平移时，使用固定的基础范围避免跳动
            # 这样即使等候区域的对象变化，视图范围也能保持稳定
            if self.zoom_scale != 1.0 or self.view_center is not None:
                # 使用固定的基础Y范围，不受等候区域影响
                # 保证至少显示观众区域到后台区域的完整范围
                fixed_base_y_min = -max(2.0, min_audience_height)
                fixed_base_y_max = self.stage_height + backstage_height + 1
                
                # 计算视图中心
                if self.view_center is not None:
                    x_center, y_center = self.view_center
                else:
                    x_center = (base_x_min + base_x_max) / 2
                    y_center = (fixed_base_y_min + fixed_base_y_max) / 2
                
                # 应用缩放（使用固定基础范围）
                x_range = (base_x_max - base_x_min) / self.zoom_scale
                y_range = (fixed_base_y_max - fixed_base_y_min) / self.zoom_scale
            else:
                # 默认视图模式，使用动态计算的范围
                x_center = (base_x_min + base_x_max) / 2
                y_center = (base_y_min + base_y_max) / 2
                
                x_range = (base_x_max - base_x_min)
                y_range = (base_y_max - base_y_min)
            
            self.ax.set_xlim(x_center - x_range/2, x_center + x_range/2)
            self.ax.set_ylim(y_center - y_range/2, y_center + y_range/2)
        
        # 设置固定的长宽比，确保舞台和对象不会变形
        # 使用 'datalim' 让坐标轴可以调整大小，同时保持数据的长宽比
        self.ax.set_aspect('equal', adjustable='datalim')
        
        # 设置坐标轴刻度，与辅助线间隔对应
        if self.grid_enabled.get() and self.grid_interval_x >= 0.1 and self.grid_interval_y >= 0.1:
            # 使用辅助线间隔作为坐标轴刻度间隔
            xlim = self.ax.get_xlim()
            ylim = self.ax.get_ylim()
            
            # 安全检查：限制最大刻度数量
            max_ticks = 200
            
            # 计算X轴刻度位置
            x_ticks = []
            x_tick_count = 0
            x = 0
            while x <= xlim[1] and x_tick_count < max_ticks:
                x_ticks.append(x)
                x += self.grid_interval_x
                x_tick_count += 1
            x = -self.grid_interval_x
            while x >= xlim[0] and x_tick_count < max_ticks:
                x_ticks.append(x)
                x -= self.grid_interval_x
                x_tick_count += 1
            x_ticks.sort()
            
            # 计算Y轴刻度位置
            y_ticks = []
            y_tick_count = 0
            y = 0
            while y <= ylim[1] and y_tick_count < max_ticks:
                y_ticks.append(y)
                y += self.grid_interval_y
                y_tick_count += 1
            y = -self.grid_interval_y
            while y >= ylim[0] and y_tick_count < max_ticks:
                y_ticks.append(y)
                y -= self.grid_interval_y
                y_tick_count += 1
            y_ticks.sort()
            
            # 设置刻度（只显示数字，不显示刻度线）
            self.ax.set_xticks(x_ticks)
            self.ax.set_yticks(y_ticks)
            # 完全隐藏刻度线，只保留刻度标签
            self.ax.tick_params(axis='both', length=0)  # 刻度线长度设为0
            # 显示刻度标签
            self.ax.tick_params(axis='both', labelbottom=True, labelleft=True)
            # 关闭matplotlib的网格，完全使用自定义辅助线
            self.ax.grid(False)
        else:
            # 辅助线未启用时，隐藏所有刻度
            self.ax.set_xticks([])
            self.ax.set_yticks([])
            # 隐藏刻度标签
            self.ax.tick_params(axis='both', labelbottom=False, labelleft=False)
            # 关闭网格
            self.ax.grid(False)
        
        
        # 绘制舞台边界
        stage_rect = Rectangle((-self.stage_width/2, 0), self.stage_width, self.stage_height, 
                             fill=False, color='black', linewidth=2)
        self.ax.add_patch(stage_rect)
        
        # 绘制舞台中线（红色虚线，从底部到顶部）
        self.ax.plot([0, 0], [0, self.stage_height], 'r--', linewidth=0.8, alpha=0.5, label='中线')
        
        # 绘制舞台区域标记
        self.ax.axhline(y=0, color='gray', linestyle='--', alpha=0.5)  # 添加舞台边界线
        self.ax.axhline(y=self.stage_height, color='gray', linestyle='--', alpha=0.5)  # 添加舞台顶部边界线
        self.ax.axvline(x=-self.stage_width/2, color='gray', linestyle='--', alpha=0.5)  # 添加左侧边界线
        self.ax.axvline(x=self.stage_width/2, color='gray', linestyle='--', alpha=0.5)  # 添加右侧边界线
        
        # 绘制不可见区域标识
        # 左侧不可见区域
        left_invisible = Rectangle((-self.stage_width/2 - invisible_width, 0), 
                                 invisible_width, self.stage_height,
                                 fill=True, color='gray', alpha=0.3)
        self.ax.add_patch(left_invisible)
        self.ax.text(-self.stage_width/2 - invisible_width/2, self.stage_height/2, '左侧\n备台区域', 
                     rotation=90, ha='center', va='center', color='gray', alpha=0.7, fontsize=12)
        
        # 右侧不可见区域
        right_invisible = Rectangle((self.stage_width/2, 0), 
                                  invisible_width, self.stage_height,
                                  fill=True, color='gray', alpha=0.3)
        self.ax.add_patch(right_invisible)
        self.ax.text(self.stage_width/2 + invisible_width/2, self.stage_height/2, '右侧\n备台区域', 
                     rotation=90, ha='center', va='center', color='gray', alpha=0.7, fontsize=12)
        
        # 后方备台区域 - 在舞台上方增加一个备台区域，连接左右两侧
        backstage_height = self.stage_height / 8  # 后方备台区域高度为舞台高度的1/8
        # 扩展后方备台区域，覆盖整个宽度包括左右两侧
        upper_backstage = Rectangle((-self.stage_width/2 - invisible_width, self.stage_height), 
                                   self.stage_width + 2 * invisible_width, backstage_height,
                                   fill=True, color='gray', alpha=0.3)
        self.ax.add_patch(upper_backstage)
        self.ax.text(0, self.stage_height + backstage_height/2, '后方备台区域', 
                     ha='center', va='center', color='gray', alpha=0.7, fontsize=12)
        
        # 添加区域标识 - 根据实际内容调整位置
        if min_y < 0:
            self.ax.text(0, min_y/2, '观众区域', ha='center', va='center', color='gray', alpha=0.7)
        
        # 绘制自定义辅助线（如果启用）
        if self.grid_enabled.get():
            # 获取当前视图范围
            xlim = self.ax.get_xlim()
            ylim = self.ax.get_ylim()
            
            # 计算辅助线的起止位置，覆盖整个可见区域
            x_start = xlim[0]
            x_end = xlim[1]
            y_start = ylim[0]
            y_end = ylim[1]
            
            # 安全检查：防止间隔过小导致性能问题
            min_interval = 0.1  # 最小间隔
            max_lines = 200  # 每个方向最大辅助线数量
            
            # 绘制垂直辅助线（X方向）
            if self.grid_interval_x >= min_interval:
                x_line_count = 0
                # 计算第一条线的位置（从0开始向两侧延伸）
                x = 0
                # 向右绘制
                while x <= x_end and x_line_count < max_lines:
                    if x >= x_start:  # 只绘制在可见范围内的线
                        self.ax.plot([x, x], [y_start, y_end], 
                                   color=self.grid_color, 
                                   linestyle=self.grid_linestyle,
                                   linewidth=self.grid_linewidth,
                                   alpha=self.grid_alpha,
                                   zorder=0)  # zorder=0确保在背景
                        x_line_count += 1
                    x += self.grid_interval_x
                
                # 向左绘制
                x = -self.grid_interval_x
                while x >= x_start and x_line_count < max_lines:
                    if x <= x_end:  # 只绘制在可见范围内的线
                        self.ax.plot([x, x], [y_start, y_end], 
                                   color=self.grid_color, 
                                   linestyle=self.grid_linestyle,
                                   linewidth=self.grid_linewidth,
                                   alpha=self.grid_alpha,
                                   zorder=0)
                        x_line_count += 1
                    x -= self.grid_interval_x
            
            # 绘制水平辅助线（Y方向）
            if self.grid_interval_y >= min_interval:
                y_line_count = 0
                # 计算第一条线的位置（从0开始向上下延伸）
                y = 0
                # 向上绘制
                while y <= y_end and y_line_count < max_lines:
                    if y >= y_start:  # 只绘制在可见范围内的线
                        self.ax.plot([x_start, x_end], [y, y], 
                                   color=self.grid_color, 
                                   linestyle=self.grid_linestyle,
                                   linewidth=self.grid_linewidth,
                                   alpha=self.grid_alpha,
                                   zorder=0)
                        y_line_count += 1
                    y += self.grid_interval_y
                
                # 向下绘制
                y = -self.grid_interval_y
                while y >= y_start and y_line_count < max_lines:
                    if y <= y_end:  # 只绘制在可见范围内的线
                        self.ax.plot([x_start, x_end], [y, y], 
                                   color=self.grid_color, 
                                   linestyle=self.grid_linestyle,
                                   linewidth=self.grid_linewidth,
                                   alpha=self.grid_alpha,
                                   zorder=0)
                        y_line_count += 1
                    y -= self.grid_interval_y
        
        # 绘制所有演员
        for actor in self.actors:
            # 获取当前位置
            if actor["keyframes"]:  # 如果有关键帧
                # 找到当前帧之前和之后的关键帧
                prev_frame = max([f for f in actor["keyframes"] if f <= self.current_frame], default=None)
                next_frame = min([f for f in actor["keyframes"] if f > self.current_frame], default=None)
                
                if prev_frame is not None:
                    if next_frame is not None:
                        # 在两个关键帧之间进行插值
                        pos = actor["positions"][self.current_frame]
                    else:
                        # 使用最后一个关键帧的位置
                        pos = actor["positions"][prev_frame]
                else:
                    # 使用初始位置
                    pos = actor["positions"][0]
            else:
                # 没有关键帧时使用初始位置
                pos = actor["positions"][0]
            
            # 检查是否有临时位置覆盖
            actor_id = self.get_element_id(actor)
            if actor_id in self.temp_position_overrides:
                pos = self.temp_position_overrides[actor_id]
            
            # 获取颜色，如果没有颜色属性则使用默认颜色
            color = actor.get("color", "blue")
            # 获取字号，如果没有字号属性则使用默认字号
            font_size = actor.get("font_size", 10)
            
            # 获取当前帧的名称字符样式
            name_styles_array = actor.get("name_char_styles_per_frame", [])
            char_styles = name_styles_array[self.current_frame] if self.current_frame < len(name_styles_array) else []
            
            # 检查是否被选中
            is_selected = any(item['item'] is actor for item in self.selected_items)
            
            # 获取当前帧的旋转角度
            rotation = 0.0
            if "rotations" in actor and actor["rotations"]:
                if self.current_frame < len(actor["rotations"]):
                    rotation = actor["rotations"][self.current_frame]
            
            # 获取当前帧的样式（新版样式系统）
            if "styles_per_frame" in actor and len(actor["styles_per_frame"]) > self.current_frame:
                frame_style = actor["styles_per_frame"][self.current_frame]
                border_color = frame_style.get("border_color", color)
                border_width = frame_style.get("border_width", 2)
                border_style = frame_style.get("border_style", "solid")
                border_alpha = frame_style.get("border_alpha", 1.0)
                fill_enabled = frame_style.get("fill_enabled", False)
                fill_color = frame_style.get("fill_color", color)
                fill_alpha = frame_style.get("fill_alpha", 1.0)
                text_color = frame_style.get("text_color", color)
                text_size = frame_style.get("text_size", font_size)
            else:
                # 向后兼容：使用旧的全局样式
                border_color = color
                border_width = 2
                border_style = "solid"
                border_alpha = 1.0
                fill_enabled = actor.get("fill_enabled", False)
                fill_color = color
                fill_alpha = actor.get("fill_alpha", 1.0)
                text_color = color
                text_size = font_size
            
            # 线宽：选中时加粗
            linewidth = border_width + 1 if is_selected else border_width
            
            # 线形映射
            linestyle_map = {"solid": "-", "dashed": "--", "dotted": ":", "dashdot": "-."}
            linestyle = linestyle_map.get(border_style, "-")
            
            # 绘制演员
            if actor["shape"] == "circle":
                # size是直径，计算半径
                radius = actor["size"] / 2
                circle = Circle((pos[0], pos[1]), radius, 
                             fill=fill_enabled,
                             facecolor=fill_color if fill_enabled else 'none',
                             edgecolor=border_color,
                             alpha=fill_alpha if fill_enabled else border_alpha,
                             linewidth=linewidth,
                             linestyle=linestyle)
                # 应用旋转变换（取负号：用户定义正数=顺时针，matplotlib正数=逆时针）
                t = transforms.Affine2D().rotate_deg_around(pos[0], pos[1], -rotation) + self.ax.transData
                circle.set_transform(t)
                self.ax.add_patch(circle)
                # 如果被选中，添加外圈高亮
                if is_selected:
                    highlight = Circle((pos[0], pos[1]), radius * 1.15, 
                                     fill=False, color='yellow', linewidth=2, 
                                     linestyle='--', alpha=0.7)
                    highlight.set_transform(t)
                    self.ax.add_patch(highlight)
                # 使用带样式的名称渲染（使用新的文本颜色和字号）
                self.render_styled_name(self.ax, pos, actor["name"], text_size, text_color, char_styles, is_export=False, rotation=rotation)
            elif actor["shape"] == "square":
                rect = Rectangle((pos[0]-actor["size"]/2, pos[1]-actor["size"]/2),
                               actor["size"], actor["size"], 
                               fill=fill_enabled,
                               facecolor=fill_color if fill_enabled else 'none',
                               edgecolor=border_color,
                               alpha=fill_alpha if fill_enabled else border_alpha,
                               linewidth=linewidth,
                               linestyle=linestyle)
                # 应用旋转变换（取负号：用户定义正数=顺时针，matplotlib正数=逆时针）
                t = transforms.Affine2D().rotate_deg_around(pos[0], pos[1], -rotation) + self.ax.transData
                rect.set_transform(t)
                self.ax.add_patch(rect)
                # 如果被选中，添加外框高亮
                if is_selected:
                    margin = actor["size"] * 0.15
                    highlight = Rectangle((pos[0]-actor["size"]/2-margin, pos[1]-actor["size"]/2-margin),
                                        actor["size"]+2*margin, actor["size"]+2*margin, 
                                        fill=False, color='yellow', linewidth=2, 
                                        linestyle='--', alpha=0.7)
                    highlight.set_transform(t)
                    self.ax.add_patch(highlight)
                # 使用带样式的名称渲染
                self.render_styled_name(self.ax, pos, actor["name"], text_size, text_color, char_styles, is_export=False, rotation=rotation)
            elif actor["shape"] == "triangle":
                triangle = Polygon([(pos[0], pos[1]+actor["size"]),
                                  (pos[0]-actor["size"], pos[1]-actor["size"]),
                                  (pos[0]+actor["size"], pos[1]-actor["size"])], 
                                 fill=fill_enabled,
                                 facecolor=fill_color if fill_enabled else 'none',
                                 edgecolor=border_color,
                                 alpha=fill_alpha if fill_enabled else border_alpha,
                                 linewidth=linewidth,
                                 linestyle=linestyle)
                # 应用旋转变换（取负号：用户定义正数=顺时针，matplotlib正数=逆时针）
                t = transforms.Affine2D().rotate_deg_around(pos[0], pos[1], -rotation) + self.ax.transData
                triangle.set_transform(t)
                self.ax.add_patch(triangle)
                # 如果被选中，添加外框高亮
                if is_selected:
                    margin = actor["size"] * 0.15
                    highlight = Rectangle((pos[0]-actor["size"]-margin, pos[1]-actor["size"]-margin),
                                        2*(actor["size"]+margin), 2*(actor["size"]+margin), 
                                        fill=False, color='yellow', linewidth=2, 
                                        linestyle='--', alpha=0.7)
                    highlight.set_transform(t)
                    self.ax.add_patch(highlight)
                # 使用带样式的名称渲染
                self.render_styled_name(self.ax, pos, actor["name"], text_size, text_color, char_styles, is_export=False, rotation=rotation)
        
        # 绘制所有道具
        for prop in self.props:
            # 获取当前位置
            if prop["keyframes"]:  # 如果有关键帧
                # 找到当前帧之前和之后的关键帧
                prev_frame = max([f for f in prop["keyframes"] if f <= self.current_frame], default=None)
                next_frame = min([f for f in prop["keyframes"] if f > self.current_frame], default=None)
                
                if prev_frame is not None:
                    if next_frame is not None:
                        # 在两个关键帧之间进行插值
                        pos = prop["positions"][self.current_frame]
                    else:
                        # 使用最后一个关键帧的位置
                        pos = prop["positions"][prev_frame]
                else:
                    pos = prop["positions"][0]
            else:
                pos = prop["positions"][0]
            
            # 检查是否有临时位置覆盖
            prop_id = self.get_element_id(prop)
            if prop_id in self.temp_position_overrides:
                pos = self.temp_position_overrides[prop_id]
                
            # 获取颜色，如果没有颜色属性则使用默认颜色
            color = prop.get("color", "red")
            # 获取字号，如果没有字号属性则使用默认字号
            font_size = prop.get("font_size", 10)
            
            # 获取当前帧的名称字符样式
            name_styles_array = prop.get("name_char_styles_per_frame", [])
            char_styles = name_styles_array[self.current_frame] if self.current_frame < len(name_styles_array) else []
            
            # 检查是否被选中
            is_selected = any(item['item'] is prop for item in self.selected_items)
            
            # 获取当前帧的旋转角度
            rotation = 0.0
            if "rotations" in prop and prop["rotations"]:
                if self.current_frame < len(prop["rotations"]):
                    rotation = prop["rotations"][self.current_frame]
                
            # 获取当前帧的样式（新版样式系统）
            if "styles_per_frame" in prop and len(prop["styles_per_frame"]) > self.current_frame:
                frame_style = prop["styles_per_frame"][self.current_frame]
                border_color = frame_style.get("border_color", color)
                border_width = frame_style.get("border_width", 2)
                border_style = frame_style.get("border_style", "solid")
                border_alpha = frame_style.get("border_alpha", 1.0)
                fill_enabled = frame_style.get("fill_enabled", False)
                fill_color = frame_style.get("fill_color", color)
                fill_alpha = frame_style.get("fill_alpha", 1.0)
                text_color = frame_style.get("text_color", color)
                text_size = frame_style.get("text_size", font_size)
            else:
                # 向后兼容：使用旧的全局样式
                border_color = color
                border_width = 2
                border_style = "solid"
                border_alpha = 1.0
                fill_enabled = prop.get("fill_enabled", False)
                fill_color = color
                fill_alpha = prop.get("fill_alpha", 1.0)
                text_color = color
                text_size = font_size
            
            # 线宽：选中时加粗
            linewidth = border_width + 1 if is_selected else border_width
            
            # 线形映射
            linestyle_map = {"solid": "-", "dashed": "--", "dotted": ":", "dashdot": "-."}
            linestyle = linestyle_map.get(border_style, "-")
                
            if prop["shape"] == "rectangle":
                rect = Rectangle((pos[0]-prop["width"]/2, pos[1]-prop["height"]/2),
                               prop["width"], prop["height"], 
                               fill=fill_enabled,
                               facecolor=fill_color if fill_enabled else 'none',
                               edgecolor=border_color,
                               alpha=fill_alpha if fill_enabled else border_alpha,
                               linewidth=linewidth,
                               linestyle=linestyle)
                # 应用旋转变换（取负号：用户定义正数=顺时针，matplotlib正数=逆时针）
                t = transforms.Affine2D().rotate_deg_around(pos[0], pos[1], -rotation) + self.ax.transData
                rect.set_transform(t)
                self.ax.add_patch(rect)
                # 如果被选中，添加外框高亮
                if is_selected:
                    margin_w = prop["width"] * 0.15
                    margin_h = prop["height"] * 0.15
                    highlight = Rectangle((pos[0]-prop["width"]/2-margin_w, pos[1]-prop["height"]/2-margin_h),
                                        prop["width"]+2*margin_w, prop["height"]+2*margin_h, 
                                        fill=False, color='yellow', linewidth=2, 
                                        linestyle='--', alpha=0.7)
                    highlight.set_transform(t)
                    self.ax.add_patch(highlight)
                # 使用带样式的名称渲染
                self.render_styled_name(self.ax, pos, prop["name"], text_size, text_color, char_styles, is_export=False, rotation=rotation)
            elif prop["shape"] == "circle":
                circle = Circle((pos[0], pos[1]), prop["width"]/2, 
                             fill=fill_enabled,
                             facecolor=fill_color if fill_enabled else 'none',
                             edgecolor=border_color,
                             alpha=fill_alpha if fill_enabled else border_alpha,
                             linewidth=linewidth,
                             linestyle=linestyle)
                # 应用旋转变换（取负号：用户定义正数=顺时针，matplotlib正数=逆时针）
                t = transforms.Affine2D().rotate_deg_around(pos[0], pos[1], -rotation) + self.ax.transData
                circle.set_transform(t)
                self.ax.add_patch(circle)
                # 如果被选中，添加外圈高亮
                if is_selected:
                    highlight = Circle((pos[0], pos[1]), prop["width"]/2 * 1.15, 
                                     fill=False, color='yellow', linewidth=2, 
                                     linestyle='--', alpha=0.7)
                    highlight.set_transform(t)
                    self.ax.add_patch(highlight)
                # 使用带样式的名称渲染
                self.render_styled_name(self.ax, pos, prop["name"], text_size, text_color, char_styles, is_export=False, rotation=rotation)
            elif prop["shape"] == "triangle":
                triangle = Polygon([(pos[0], pos[1]+prop["height"]/2),
                                  (pos[0]-prop["width"]/2, pos[1]-prop["height"]/2),
                                  (pos[0]+prop["width"]/2, pos[1]-prop["height"]/2)], 
                                 fill=fill_enabled,
                                 facecolor=fill_color if fill_enabled else 'none',
                                 edgecolor=border_color,
                                 alpha=fill_alpha if fill_enabled else border_alpha,
                                 linewidth=linewidth,
                                 linestyle=linestyle)
                # 应用旋转变换（取负号：用户定义正数=顺时针，matplotlib正数=逆时针）
                t = transforms.Affine2D().rotate_deg_around(pos[0], pos[1], -rotation) + self.ax.transData
                triangle.set_transform(t)
                self.ax.add_patch(triangle)
                # 如果被选中，添加外框高亮
                if is_selected:
                    margin_w = prop["width"]/2 * 0.15
                    margin_h = prop["height"]/2 * 0.15
                    highlight = Rectangle((pos[0]-prop["width"]/2-margin_w, pos[1]-prop["height"]/2-margin_h),
                                        prop["width"]+2*margin_w, prop["height"]+2*margin_h, 
                                        fill=False, color='yellow', linewidth=2, 
                                        linestyle='--', alpha=0.7)
                    highlight.set_transform(t)
                    self.ax.add_patch(highlight)
                # 使用带样式的名称渲染
                self.render_styled_name(self.ax, pos, prop["name"], text_size, text_color, char_styles, is_export=False, rotation=rotation)
        
        # 计算实际的视图缩放比例（用于文本框字号缩放）
        # 必须在绘制文本框之前计算，此时xlim已经被set_aspect调整过
        invisible_width = self.stage_width / 8
        initial_x_range = (self.stage_width + 2 * invisible_width)
        current_xlim = self.ax.get_xlim()
        current_x_range = current_xlim[1] - current_xlim[0]
        actual_view_scale = initial_x_range / current_x_range if current_x_range > 0 else 1.0
        # 限制在合理范围内：缩小到30%，放大到110%（匹配画布实际限制）
        self.actual_view_scale = max(0.3, min(1.1, actual_view_scale))
        
        # 调试：输出缩放信息（每30帧输出一次，避免刷屏）
        if self.current_frame % 30 == 0 or abs(self.zoom_scale - self.actual_view_scale) > 0.1:
            print(f"🔍 缩放调试 | zoom_scale={self.zoom_scale:.2f} | actual_view_scale={self.actual_view_scale:.2f} | x_range={current_x_range:.2f}")
        
        # 绘制文本框（支持多个独立文本框，持续时间控制，每帧不同内容和样式）
        for i, textbox in enumerate(self.textboxes):
            # 检查是否在显示时间范围内
            start_frame = textbox.get("start_frame", 0)
            duration_frames = textbox.get("duration_frames", self.total_frames)
            end_frame = start_frame + duration_frames
            
            # 只在时间范围内显示
            if not (start_frame <= self.current_frame < end_frame):
                continue
            
            # 获取当前位置
            if textbox["keyframes"]:
                prev_frame = max([f for f in textbox["keyframes"] if f <= self.current_frame], default=None)
                next_frame = min([f for f in textbox["keyframes"] if f > self.current_frame], default=None)
                
                if prev_frame is not None:
                    if next_frame is not None:
                        pos = textbox["positions"][self.current_frame]
                    else:
                        pos = textbox["positions"][prev_frame]
                else:
                    pos = textbox["positions"][0]
            else:
                pos = textbox["positions"][0]
            
            # 检查文本框是否被选中
            is_selected = any(
                item['type'] == 'textbox' and item['item'] is textbox
                for item in self.selected_items
            )
            
            # 设置边框样式
            if is_selected:
                edgecolor = 'yellow'
                linewidth = 2
            else:
                edgecolor = 'gray'
                linewidth = 1
            
            # 获取当前帧的内容和字符样式
            contents_array = textbox.get("contents", [])
            char_styles_array = textbox.get("char_styles_per_frame", [])
            
            # 获取当前帧的内容
            if self.current_frame < len(contents_array):
                content = contents_array[self.current_frame]
            else:
                content = ""
            
            # 如果内容为空，跳过不渲染
            if not content:
                continue
            
            # 获取当前帧的字符样式
            if self.current_frame < len(char_styles_array):
                char_styles = char_styles_array[self.current_frame]
            else:
                char_styles = []
            
            # 验证字符样式数组的有效性
            # 必须同时满足：1)存在 2)长度匹配 3)不是空列表 4)所有样式对象都有效
            has_valid_styles = False
            if char_styles and len(char_styles) == len(content) and len(char_styles) > 0:
                # 进一步验证每个样式对象是否有效
                all_styles_valid = all(
                    isinstance(style, dict) and 
                    "font_size" in style and 
                    "color" in style 
                    for style in char_styles
                )
                has_valid_styles = all_styles_valid
            
            # 检查是否所有字符样式完全相同（提前判断以避免不必要的处理）
            if has_valid_styles:
                first_style = char_styles[0]
                all_same_style = all(
                    s["font_size"] == first_style["font_size"] and 
                    s["color"] == first_style["color"] 
                    for s in char_styles
                )
            else:
                all_same_style = False
            
            # 如果没有样式或所有样式相同，使用整体绘制（避免间距问题）
            if not has_valid_styles or all_same_style:
                # 确定字号和颜色
                if has_valid_styles:
                    use_font_size = char_styles[0]["font_size"]
                    use_color = char_styles[0]["color"]
                else:
                    use_font_size = textbox.get("default_font_size", 12)
                    use_color = textbox.get("default_color", "black")
                
                # 根据实际视图缩放比例调整字号
                scaled_font_size = use_font_size * self.actual_view_scale
                
                # 简单模式：整体绘制（统一间距）
                text_obj = self.ax.text(pos[0], pos[1],
                            content,
                            ha='center', va='center',
                            fontsize=scaled_font_size,
                            color=use_color,
                            bbox=dict(facecolor='white', alpha=0.8, edgecolor=edgecolor, linewidth=linewidth, pad=3))
                # 如果被选中，添加外框高亮
                if is_selected:
                    bbox = text_obj.get_window_extent(renderer=self.fig.canvas.get_renderer())  # type: ignore
                    bbox_data = bbox.transformed(self.ax.transData.inverted())
                    margin_x = (bbox_data.width) * 0.15
                    margin_y = (bbox_data.height) * 0.15
                    from matplotlib.patches import Rectangle as HighlightRect
                    highlight = HighlightRect((bbox_data.x0 - margin_x, bbox_data.y0 - margin_y),
                                            bbox_data.width + 2*margin_x, bbox_data.height + 2*margin_y,
                                            fill=False, color='yellow', linewidth=2,
                                            linestyle='--', alpha=0.7)
                    self.ax.add_patch(highlight)
            else:
                # 多种样式，逐字符绘制
                # 先计算每个字符的信息和总宽度
                char_info_list = []
                max_font_size = 0
                
                for j, char in enumerate(content):
                    if j < len(char_styles):
                        char_font_size = char_styles[j].get("font_size", 12)
                        char_color = char_styles[j].get("color", "black")
                    else:
                        char_font_size = 12
                        char_color = "black"
                    
                    # 根据实际视图缩放比例调整字号
                    scaled_font_size = char_font_size * self.actual_view_scale
                    
                    # 计算字符宽度（使用缩放后的字号，保持一致性）
                    char_width = scaled_font_size * 0.048
                    
                    char_info_list.append({
                        "char": char,
                        "font_size": scaled_font_size,  # 使用缩放后的字号
                        "color": char_color,
                        "width": char_width
                    })
                    max_font_size = max(max_font_size, scaled_font_size)
                
                # 计算总宽度
                total_width = sum(c["width"] for c in char_info_list)
                
                # 多种样式，逐字符绘制
                # 绘制背景框
                from matplotlib.patches import FancyBboxPatch
                # 根据最大字号计算适当的padding和高度
                padding = max_font_size * 0.01  # padding随字号缩放
                bg_height = max_font_size * 0.025  # 增加背景框高度
                bg_bbox = FancyBboxPatch(
                    (pos[0] - total_width/2 - padding, pos[1] - bg_height/2 - padding),
                    total_width + padding*2, bg_height + padding*2,
                    boxstyle="round,pad=0.02", 
                    facecolor='white', alpha=0.8, 
                    edgecolor=edgecolor, linewidth=linewidth)
                self.ax.add_patch(bg_bbox)
                
                # 如果被选中，添加外框高亮
                if is_selected:
                    highlight_padding = padding * 2
                    highlight_bbox = FancyBboxPatch(
                        (pos[0] - total_width/2 - highlight_padding, pos[1] - bg_height/2 - highlight_padding),
                        total_width + highlight_padding*2, bg_height + highlight_padding*2,
                        boxstyle="round,pad=0.02",
                        fill=False, edgecolor='yellow', linewidth=2,
                        linestyle='--', alpha=0.7)
                    self.ax.add_patch(highlight_bbox)
                
                # 逐字符绘制，从左到右
                current_x = pos[0] - total_width / 2
                # 使用统一的Y坐标基线，确保所有字符对齐在同一基线上
                base_y = pos[1]
                
                for char_info in char_info_list:
                    # 计算字符中心位置
                    char_center_x = current_x + char_info["width"] / 2
                    
                    # 绘制字符（使用center对齐，与整体绘制保持一致）
                    self.ax.text(char_center_x, base_y, char_info["char"],
                               ha='center', va='center',
                               fontsize=char_info["font_size"],
                               color=char_info["color"])
                    
                    # 移动到下一个字符位置
                    current_x += char_info["width"]
        
        # 设置坐标轴标签（只在舞台区域显示）
        self.ax.set_xlabel('X', fontsize=8)
        self.ax.set_ylabel('Y', fontsize=8)
        
        # 设置标题 - 减小pad值，避免标题过于上移
        self.ax.set_title(f'当前时间: {self.current_second:.1f}秒', fontsize=12, pad=5)
        
        # 自定义刻度格式化函数
        def format_func(value, pos):
            if value.is_integer():
                return f'{int(value)}'
            else:
                return f'{value:.1f}'
        
        # 设置刻度格式
        self.ax.xaxis.set_major_formatter(FuncFormatter(format_func))
        self.ax.yaxis.set_major_formatter(FuncFormatter(format_func))
        
        # 设置X轴刻度位置在Y=0线（恢复原有设置）
        self.ax.xaxis.set_ticks_position('bottom')
        self.ax.xaxis.set_label_position('bottom')
        self.ax.spines['bottom'].set_position(('data', 0))
        
        # 完全隐藏坐标轴边框（spines）
        self.ax.spines['left'].set_visible(False)
        self.ax.spines['right'].set_visible(False)
        self.ax.spines['top'].set_visible(False)
        self.ax.spines['bottom'].set_visible(False)  # 隐藏底部边框，刻度仍显示在Y=0
        
        # 绘制矩形框选框（如果正在框选）
        if self.rect_selecting and self.rect_select_start and self.rect_select_end:
            x1, y1 = self.rect_select_start
            x2, y2 = self.rect_select_end
            # 计算矩形的左下角坐标和宽高
            rect_x = min(x1, x2)
            rect_y = min(y1, y2)
            rect_width = abs(x2 - x1)
            rect_height = abs(y2 - y1)
            # 绘制半透明的矩形框
            rect_box = Rectangle((rect_x, rect_y), rect_width, rect_height,
                                fill=True, facecolor='cyan', alpha=0.2,
                                edgecolor='blue', linewidth=2, linestyle='--')
            self.ax.add_patch(rect_box)
        
        # 绘制智能对齐辅助线
        if hasattr(self, 'align_guides') and len(self.align_guides) > 0:
            for guide in self.align_guides:
                x1, y1, x2, y2, guide_type = guide
                self.ax.plot([x1, x2], [y1, y2], 
                           color='magenta', linewidth=1.5, 
                           linestyle='--', alpha=0.8, zorder=1000)
        
        # 调整布局以适应容器大小
        # 注意：避免在每次更新时调用 tight_layout，因为可能导致窗口移动
        # 只在必要时调用（如窗口大小改变时）
        # try:
        #     self.fig.tight_layout(pad=0.5)
        # except:
        #     pass  # 如果 tight_layout 失败，忽略错误继续
        
        # 使用 draw_idle() 而不是 draw()，避免阻塞音频播放
        # draw_idle() 会在下一个空闲周期绘制，不会立即阻塞主线程
        self.canvas.draw_idle()

    def calculate_layout_parameters(self):
        """计算布局参数"""
        # 观众区域位置（舞台下方）
        audience_start_y = -1.5  # 观众区域起始位置
        
        # 基础参数
        min_spacing = 0.8  # 最小间距
        max_elements_per_row = max(1, int((self.stage_width - 1) / min_spacing))  # 每行最大元素数
        
        return {
            'audience_start_y': audience_start_y,
            'min_spacing': min_spacing,
            'max_elements_per_row': max_elements_per_row,
            'stage_width': self.stage_width
        }
    
    def get_waiting_area_actors(self):
        """获取在等候区域的演员（当前帧位置在观众区域的演员）"""
        params = self.calculate_layout_parameters()
        waiting_actors = []
        for actor in self.actors:
            current_pos = actor["positions"][self.current_frame]
            if current_pos[1] <= params['audience_start_y']:
                waiting_actors.append(actor)
        return waiting_actors
    
    def get_waiting_area_props(self):
        """获取在等候区域的道具（当前帧位置在观众区域的道具）"""
        params = self.calculate_layout_parameters()
        waiting_props = []
        for prop in self.props:
            current_pos = prop["positions"][self.current_frame]
            if current_pos[1] <= params['audience_start_y']:
                waiting_props.append(prop)
        return waiting_props

    def calculate_element_size(self, element, element_type):
        """计算元素的实际占用空间"""
        if element_type == "actor":
            return element["size"]  # size已经是直径（或边长）
        else:  # prop
            return max(element["width"], element["height"])
    
    def arrange_waiting_area(self):
        """重新排列等候区域的所有演员和道具"""
        params = self.calculate_layout_parameters()
        waiting_actors = self.get_waiting_area_actors()
        waiting_props = self.get_waiting_area_props()
        
        # 将演员和道具合并，按添加顺序排序
        all_elements = []
        for actor in waiting_actors:
            all_elements.append(('actor', actor))
        for prop in waiting_props:
            all_elements.append(('prop', prop))
        
        if not all_elements:
            return
        
        # 计算布局
        current_x = -self.stage_width / 2 + 0.5  # 从左边开始，留一点边距
        current_y = params['audience_start_y']
        current_row_elements = 0
        max_height_in_row = 0
        
        for element_type, element in all_elements:
            element_size = self.calculate_element_size(element, element_type)
            
            # 检查是否需要换行
            if (current_x + element_size > self.stage_width / 2 - 0.5 or 
                current_row_elements >= params['max_elements_per_row']):
                # 换行
                current_x = -self.stage_width / 2 + 0.5
                current_y -= (max_height_in_row + params['min_spacing'])
                current_row_elements = 0
                max_height_in_row = 0
            
            # 设置位置
            pos_x = current_x + element_size / 2
            pos_y = current_y
            
            # 只为没有关键帧的元素（新添加的元素）设置位置和关键帧
            # 已有关键帧的元素不应被自动修改
            if not element["keyframes"]:
                # 新元素：为所有帧设置相同的初始位置
                for frame in range(self.total_frames):
                    element["positions"][frame] = (pos_x, pos_y)
            
            # 更新布局参数
            current_x += element_size + params['min_spacing']
            current_row_elements += 1
            max_height_in_row = max(max_height_in_row, element_size)
        
        print(f"重新排列了 {len(all_elements)} 个元素在等候区域")
    
    def get_element_id(self, element):
        """获取元素的唯一标识"""
        return f"{element['name']}_{id(element)}"
    
    def convert_temp_keyframe_to_permanent(self, element, frame):
        """将临时关键帧转换为正式关键帧"""
        element_id = self.get_element_id(element)
        temp_key = (element_id, frame)
        
        if temp_key in self.temp_keyframes:
            # 移除临时标记，关键帧变为正式关键帧
            del self.temp_keyframes[temp_key]
            print(f"✓ 临时关键帧转为正式关键帧: {element['name']} 在第 {frame} 帧 (剩余临时关键帧: {len(self.temp_keyframes)})")
            return True
        else:
            print(f"尝试转换临时关键帧失败: {element['name']} 在第 {frame} 帧 (不存在于临时记录中)")
            return False
    
    def cleanup_temp_keyframes_on_time_change(self):
        """当时间改变时清理不再需要的临时关键帧"""
        if not self.temp_keyframes:
            return  # 没有临时关键帧，直接返回
            
        print(f"临时关键帧清理检查 - 当前帧: {self.current_frame}, 临时关键帧数量: {len(self.temp_keyframes)}")
        to_remove = []
        
        for (element_id, frame), _ in self.temp_keyframes.items():
            # 找到对应的元素
            target_element = None
            for actor in self.actors:
                if self.get_element_id(actor) == element_id:
                    target_element = actor
                    break
            if not target_element:
                for prop in self.props:
                    if self.get_element_id(prop) == element_id:
                        target_element = prop
                        break
            
            if target_element and frame in target_element["keyframes"]:
                # 移除临时关键帧
                target_element["keyframes"].remove(frame)
                # 更新插值
                self.update_intermediate_frames(target_element)
                to_remove.append((element_id, frame))
                print(f"✓ 清理临时关键帧: {target_element['name']} 在第 {frame} 帧")
            elif not target_element:
                # 元素已经不存在，也要清理记录
                to_remove.append((element_id, frame))
                print(f"✓ 清理孤立的临时关键帧记录: {element_id} 在第 {frame} 帧")
        
        # 清理临时关键帧记录
        for key in to_remove:
            if key in self.temp_keyframes:
                del self.temp_keyframes[key]
        
        if to_remove:
            print(f"清理完成 - 清理了 {len(to_remove)} 个临时关键帧，剩余: {len(self.temp_keyframes)}")
        
        # 额外验证：检查是否有应该被清理但没有被清理的记录
        remaining_temp = list(self.temp_keyframes.keys())
        if remaining_temp:
            print(f"剩余临时关键帧: {remaining_temp}")
    
    def capture_current_view_range(self):
        """捕获当前视图范围，用于播放期间固定视图"""
        try:
            if hasattr(self, 'ax') and self.ax is not None:
                xlim = self.ax.get_xlim()
                ylim = self.ax.get_ylim()
                self.fixed_view_range = {'xlim': xlim, 'ylim': ylim}
                print(f"捕获视图范围: X={xlim}, Y={ylim}")
            else:
                print("警告: 无法捕获视图范围，ax对象不存在")
                self.fixed_view_range = None
        except Exception as e:
            print(f"捕获视图范围时出错: {e}")
            self.fixed_view_range = None
    
    def calculate_minimum_audience_height(self):
        """计算观众区域的最小高度，确保至少容纳最大元素的1.5倍"""
        max_element_size = 0
        
        # 检查所有演员的大小
        for actor in self.actors:
            if actor["shape"] == "circle":
                element_size = actor["size"]  # size已经是直径
            elif actor["shape"] == "square":
                element_size = actor["size"]  # size是边长
            elif actor["shape"] == "triangle":
                element_size = actor["size"] * 2  # size是半边长，占用空间约为2倍
            else:
                element_size = actor.get("size", 1.0)
            max_element_size = max(max_element_size, element_size)
        
        # 检查所有道具的大小
        for prop in self.props:
            element_size = max(prop["width"], prop["height"])
            max_element_size = max(max_element_size, element_size)
        
        # 最小观众区域高度为最大元素的1.5倍，但不少于2.0
        min_height = max(2.0, max_element_size * 1.5)
        print(f"计算最小观众区域高度: 最大元素={max_element_size:.2f}, 最小高度={min_height:.2f}")
        return min_height
    
    def reset_to_waiting_area(self):
        """将选中的演员或道具重置到等候区域"""
        selection = self.keyframe_listbox.curselection()
        if not selection:
            messagebox.showwarning("提示", "请先选择要重置的演员或道具")
            return
        
        # 获取选中的项目
        selected_index = selection[0]
        item_text = self.keyframe_listbox.get(selected_index)
        
        # 解析项目类型和名称
        if item_text.startswith("演员: "):
            item_type = "actor"
            item_name = item_text[4:]  # 去掉"演员: "前缀
            items_list = self.actors
        elif item_text.startswith("道具: "):
            item_type = "prop"
            item_name = item_text[4:]  # 去掉"道具: "前缀
            items_list = self.props
        else:
            messagebox.showerror("错误", "无法识别选中的项目类型")
            return
        
        # 找到对应的演员或道具
        target_item = None
        for item in items_list:
            if item["name"] == item_name:
                target_item = item
                break
        
        if not target_item:
            messagebox.showerror("错误", "找不到对应的演员或道具")
            return
        
        # 计算等候区域的新位置
        params = self.calculate_layout_parameters()
        waiting_actors = self.get_waiting_area_actors()
        waiting_props = self.get_waiting_area_props()
        
        # 计算新位置（在等候区域末尾）
        all_waiting_elements = len(waiting_actors) + len(waiting_props)
        element_size = self.calculate_element_size(target_item, item_type)
        
        # 简单布局：在等候区域从左到右排列
        new_x = -self.stage_width/2 + 0.5 + (all_waiting_elements % params['max_elements_per_row']) * (element_size + params['min_spacing']) + element_size/2
        new_y = params['audience_start_y'] - (all_waiting_elements // params['max_elements_per_row']) * (element_size + params['min_spacing'])
        
        # 设置新位置（根据是否有关键帧决定处理方式）
        if not target_item["keyframes"]:
            # 如果没有关键帧，直接设置所有帧的位置
            for frame in range(self.total_frames):
                target_item["positions"][frame] = (new_x, new_y)
        else:
            # 如果有关键帧，添加临时关键帧
            target_item["positions"][self.current_frame] = (new_x, new_y)
            if self.current_frame not in target_item["keyframes"]:
                target_item["keyframes"].append(self.current_frame)
                target_item["keyframes"].sort()
                # 标记为临时关键帧
                element_id = self.get_element_id(target_item)
                self.temp_keyframes[(element_id, self.current_frame)] = True
                print(f"✓ 添加临时关键帧: {target_item['name']} 在第 {self.current_frame} 帧")
                # 更新插值
                self.update_intermediate_frames(target_item)
        
        # 重新排列等候区域
        self.arrange_waiting_area()
        
        # 更新显示
        self.update_stage_preview()
        self.on_keyframe_list_select(None)  # 刷新关键帧列表
        
        print(f"已将 {item_name} 重置到等候区域")
    
    def reset_all_to_waiting_area(self):
        """将所有演员和道具重置到等候区域"""
        # 确认对话框
        result = messagebox.askyesno(
            "确认操作", 
            "确定要将所有演员和道具重置到等候区域吗？\n\n注意：重置时不会在当前时间点添加关键帧，但当你移动元素时，关键帧将被正确添加。",
            icon='question'
        )
        
        if not result:
            return
        
        # 计算布局参数
        params = self.calculate_layout_parameters()
        
        # 获取所有演员和道具
        all_actors = self.actors.copy()
        all_props = self.props.copy()
        
        if not all_actors and not all_props:
            messagebox.showinfo("提示", "当前没有演员或道具需要重置")
            return
        
        # 将所有元素合并进行统一布局
        all_elements = []
        for actor in all_actors:
            all_elements.append(('actor', actor))
        for prop in all_props:
            all_elements.append(('prop', prop))
        
        # 计算布局
        current_x = -self.stage_width / 2 + 0.5  # 从左边开始，留一点边距
        current_y = params['audience_start_y']
        current_row_elements = 0
        max_height_in_row = 0
        keyframe_added_count = 0
        
        for element_type, element in all_elements:
            element_size = self.calculate_element_size(element, element_type)
            
            # 检查是否需要换行
            if (current_x + element_size > self.stage_width / 2 - 0.5 or 
                current_row_elements >= params['max_elements_per_row']):
                # 换行
                current_x = -self.stage_width / 2 + 0.5
                current_y -= (max_height_in_row + params['min_spacing'])
                current_row_elements = 0
                max_height_in_row = 0
            
            # 设置位置
            pos_x = current_x + element_size / 2
            pos_y = current_y
            
            # 更新位置（根据是否有关键帧和当前时间决定处理方式）
            if not element["keyframes"]:
                # 如果没有关键帧，无论在什么时间点，都只移动位置，不设定关键帧
                for frame in range(self.total_frames):
                    element["positions"][frame] = (pos_x, pos_y)
            elif self.current_frame == 0:
                # 如果在第0帧且有关键帧，使用临时位置覆盖机制
                # 不修改实际的positions数组，而是记录临时位置覆盖
                element_id = self.get_element_id(element)
                if not hasattr(self, 'temp_position_overrides'):
                    self.temp_position_overrides = {}
                self.temp_position_overrides[element_id] = (pos_x, pos_y)
                print(f"✓ 批量重置 - 在0秒重置: {element['name']} 设置临时位置覆盖，不修改关键帧")
            else:
                # 如果有关键帧且不在第0帧，添加临时关键帧
                element["positions"][self.current_frame] = (pos_x, pos_y)
                if self.current_frame not in element["keyframes"]:
                    element["keyframes"].append(self.current_frame)
                    element["keyframes"].sort()
                    keyframe_added_count += 1
                    # 标记为临时关键帧
                    element_id = self.get_element_id(element)
                    self.temp_keyframes[(element_id, self.current_frame)] = True
                    print(f"✓ 批量重置 - 添加临时关键帧: {element['name']} 在第 {self.current_frame} 帧")
                    # 更新插值
                    self.update_intermediate_frames(element)
            
            # 更新布局参数
            current_x += element_size + params['min_spacing']
            current_row_elements += 1
            max_height_in_row = max(max_height_in_row, element_size)
        
        # 更新显示
        self.update_stage_preview()
        self.on_keyframe_list_select(None)  # 刷新关键帧列表
        
        print(f"全部重置完成：{len(all_elements)} 个元素，{keyframe_added_count} 个新关键帧")

    def on_prop_shape_change(self, event=None):
        """处理道具形状变化事件 - 圆形时隐藏高度设置"""
        selected_shape = self.prop_shape_var.get()
        
        if selected_shape == "圆形":
            # 隐藏高度输入
            self.prop_height_label.pack_forget()
            self.prop_height_entry.pack_forget()
            # 修改宽度标签为"直径"
            self.prop_width_label.config(text="直径:")
            print("道具形状：圆形 - 已隐藏高度设置，宽度改为直径")
        else:
            # 显示高度输入（需要指定pack参数以恢复到正确位置）
            self.prop_height_label.pack(side=tk.LEFT, padx=(8, 2))
            self.prop_height_entry.pack(side=tk.LEFT, padx=2)
            # 恢复宽度标签为"宽度"
            self.prop_width_label.config(text="宽度:")
            print(f"道具形状：{selected_shape} - 已显示高度设置")
    
    def apply_grid_interval(self):
        """应用辅助线间隔设置"""
        try:
            x_interval = float(self.grid_x_entry.get())
            y_interval = float(self.grid_y_entry.get())
            
            if x_interval <= 0 or y_interval <= 0:
                messagebox.showerror("错误", "间隔必须大于0")
                return
            
            self.grid_interval_x = x_interval
            self.grid_interval_y = y_interval
            
            # 更新舞台预览
            self.update_stage_preview()
            self.log(f"✓ 辅助线间隔已更新: X={x_interval:.1f}, Y={y_interval:.1f}", 'success')
            
        except ValueError:
            messagebox.showerror("错误", "请输入有效的数字")
            self.grid_x_entry.delete(0, tk.END)
            self.grid_x_entry.insert(0, f"{self.grid_interval_x:.1f}")
            self.grid_y_entry.delete(0, tk.END)
            self.grid_y_entry.insert(0, f"{self.grid_interval_y:.1f}")
    
    def on_grid_linestyle_change(self, event=None):
        """处理辅助线线形变化"""
        linestyle_map = {
            "虚线": "--",
            "实线": "-",
            "点线": ":",
            "点划线": "-."
        }
        self.grid_linestyle = linestyle_map[self.grid_linestyle_var.get()]
        self.update_stage_preview()
        self.log(f"✓ 辅助线线形已更新", 'success')
    
    def on_grid_linewidth_change(self, event=None):
        """处理辅助线线宽变化"""
        try:
            self.grid_linewidth = float(self.grid_linewidth_var.get())
            self.update_stage_preview()
            self.log(f"✓ 辅助线线宽已更新: {self.grid_linewidth}", 'success')
        except ValueError:
            messagebox.showerror("错误", "线宽值无效")
    
    def on_grid_color_change(self, event=None):
        """处理辅助线颜色变化"""
        color_map = {
            "黑色": "black",
            "灰色": "gray",
            "蓝色": "blue",
            "红色": "red",
            "绿色": "green"
        }
        self.grid_color = color_map[self.grid_color_var.get()]
        self.update_stage_preview()
        self.log(f"✓ 辅助线颜色已更新", 'success')

    def add_actor(self):
        """添加演员"""
        try:
            # 获取演员名称
            name = self.actor_name_entry.get()
            if not name:
                raise ValueError("演员名称不能为空")
            
            # 获取演员大小
            try:
                size = float(self.actor_size_entry.get())
                if size <= 0:
                    raise ValueError
            except ValueError:
                raise ValueError("演员大小必须是大于0的数字")
                
            # 获取字号
            try:
                font_size = float(self.actor_font_size.get())
                if font_size <= 0:
                    raise ValueError
            except ValueError:
                raise ValueError("字号必须是大于0的数字")
            
            # 获取颜色（使用映射后的英文颜色值）
            color = self.color_map[self.actor_color_var.get()]
            
            # 临时位置，稍后会通过arrange_waiting_area重新计算
            temp_pos = (0, -1.5)
            
            # 创建演员对象（新版完整样式系统）
            actor = {
                "name": name,
                "shape": self.actor_shape_var.get(),
                "size": size,
                "positions": [temp_pos for _ in range(self.total_frames)],
                "keyframes": [],  # 不自动创建关键帧
                "name_char_styles_per_frame": [],  # 每帧名称的字符级样式
                "rotations": [0.0 for _ in range(self.total_frames)],  # 每帧的旋转角度（度）
                "rotation_keyframes": [],  # 旋转角度关键帧
                
                # 样式关键帧系统 - 每帧的样式设置
                "styles_per_frame": [{
                    # 边框样式
                    "border_color": color,  # 边框颜色
                    "border_width": 2,  # 边框线宽
                    "border_style": "solid",  # 边框线形：solid(实线), dashed(虚线), dotted(点线), dashdot(点划线)
                    "border_alpha": 1.0,  # 边框透明度（0.0-1.0）
                    
                    # 填充样式
                "fill_enabled": False,  # 是否启用填充
                    "fill_color": color,  # 填充颜色（默认与边框相同）
                    "fill_alpha": 1.0,  # 填充透明度（0.0-1.0）
                    
                    # 文本样式
                    "text_color": color,  # 文本颜色（默认与边框相同）
                    "text_size": font_size,  # 文本字号
                    "text_bold": False,  # 文本加粗
                    "text_italic": False,  # 文本斜体
                    "text_underline": False,  # 文本下划线
                    "text_alpha": 1.0,  # 文本透明度（0.0-1.0）
                } for _ in range(self.total_frames)],
                "style_keyframes": [],  # 样式关键帧列表
                
                # 向后兼容的全局样式属性
                "color": color,
                "font_size": font_size,
                "fill_enabled": False,
                "fill_alpha": 1.0
            }
            
            # 保存历史记录
            self.save_state_to_history(f"添加演员 ({name})")
            
            self.actors.append(actor)
            
            # 重新排列等候区域
            self.arrange_waiting_area()
            
            # 更新右侧关键帧列表 - 插入到所有演员的后面、所有道具的前面
            # 索引位置应该是当前演员总数-1（因为刚刚append了新演员）
            insert_position = len(self.actors) - 1
            self.keyframe_listbox.insert(insert_position, f"演员: {actor['name']}")
            
            # 只清空名称输入框，保留其他设置
            self.actor_name_entry.delete(0, tk.END)
            
            # 更新显示
            self.update_stage_preview()
            
            # 记录日志
            self.log(f"✓ 添加演员: {name}", 'success')
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))

    def add_prop(self):
        """添加道具"""
        try:
            # 获取道具名称
            name = self.prop_name_entry.get()
            if not name:
                raise ValueError("道具名称不能为空")
            
            # 获取形状（先获取形状以确定是否需要高度）
            shape_chinese = self.prop_shape_var.get()
            shape = self.prop_shape_map[shape_chinese]
            
            # 获取道具宽度（圆形时是直径）
            try:
                width = float(self.prop_width_entry.get())
                if width <= 0:
                    raise ValueError
            except ValueError:
                if shape == "circle":
                    raise ValueError("道具直径必须是大于0的数字")
                else:
                    raise ValueError("道具宽度必须是大于0的数字")
                
            # 获取道具高度（圆形时使用宽度作为高度）
            if shape == "circle":
                height = width  # 圆形的高度等于宽度（直径）
            else:
                try:
                    height = float(self.prop_height_entry.get())
                    if height <= 0:
                        raise ValueError
                except ValueError:
                    raise ValueError("道具高度必须是大于0的数字")
                
            # 获取字号
            try:
                font_size = float(self.prop_font_size.get())
                if font_size <= 0:
                    raise ValueError
            except ValueError:
                raise ValueError("字号必须是大于0的数字")
            
            # 获取颜色（使用映射后的英文颜色值）
            color = self.color_map[self.prop_color_var.get()]
            
            # 临时位置，稍后会通过arrange_waiting_area重新计算
            temp_pos = (0, -1.5)
            
            # 创建道具对象（新版完整样式系统）
            prop = {
                "name": name,
                "shape": shape,  # 使用英文形状名
                "width": width,
                "height": height,
                "positions": [temp_pos for _ in range(self.total_frames)],
                "keyframes": [],  # 不自动创建关键帧
                "name_char_styles_per_frame": [],  # 每帧名称的字符级样式
                "rotations": [0.0 for _ in range(self.total_frames)],  # 每帧的旋转角度（度）
                "rotation_keyframes": [],  # 旋转角度关键帧
                
                # 样式关键帧系统 - 每帧的样式设置
                "styles_per_frame": [{
                    # 边框样式
                    "border_color": color,  # 边框颜色
                    "border_width": 2,  # 边框线宽
                    "border_style": "solid",  # 边框线形：solid(实线), dashed(虚线), dotted(点线), dashdot(点划线)
                    "border_alpha": 1.0,  # 边框透明度（0.0-1.0）
                    
                    # 填充样式
                "fill_enabled": False,  # 是否启用填充
                    "fill_color": color,  # 填充颜色（默认与边框相同）
                    "fill_alpha": 1.0,  # 填充透明度（0.0-1.0）
                    
                    # 文本样式
                    "text_color": color,  # 文本颜色（默认与边框相同）
                    "text_size": font_size,  # 文本字号
                    "text_bold": False,  # 文本加粗
                    "text_italic": False,  # 文本斜体
                    "text_underline": False,  # 文本下划线
                    "text_alpha": 1.0,  # 文本透明度（0.0-1.0）
                } for _ in range(self.total_frames)],
                "style_keyframes": [],  # 样式关键帧列表
                
                # 向后兼容的全局样式属性
                "color": color,
                "font_size": font_size,
                "fill_enabled": False,
                "fill_alpha": 1.0
            }
            
            # 保存历史记录
            self.save_state_to_history(f"添加道具 ({name})")
            
            self.props.append(prop)
            
            # 重新排列等候区域
            self.arrange_waiting_area()
            
            # 更新右侧关键帧列表
            self.keyframe_listbox.insert(tk.END, f"道具: {prop['name']}")
            
            # 只清空名称输入框，保留其他设置
            self.prop_name_entry.delete(0, tk.END)
            
            # 更新显示
            self.update_stage_preview()
            
            # 记录日志
            self.log(f"✓ 添加道具: {name}", 'success')
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))

    def add_textbox(self):
        """添加文本框"""
        try:
            # 获取文本框名称
            name = self.textbox_name_entry.get()
            if not name:
                raise ValueError("文本框名称不能为空")
            
            # 获取内容（Text控件）- 使用 "end-1c" 排除末尾自动添加的换行符，保留内容中的换行符
            content = self.textbox_content_entry.get("1.0", "end-1c")
            if not content.strip():  # 检查是否全是空白字符
                raise ValueError("文本框内容不能为空")
            
            # 获取字号
            try:
                font_size = float(self.textbox_font_size.get())
                if font_size <= 0:
                    raise ValueError
            except ValueError:
                raise ValueError("字号必须是大于0的数字")
            
            # 获取颜色（扩展颜色映射）
            color_map = {**self.color_map, "黑色": "black", "白色": "white"}
            color = color_map[self.textbox_color_var.get()]
            
            # 获取时间范围（开始时间和结束时间）
            try:
                start_seconds = float(self.textbox_start_time.get())
                end_seconds = float(self.textbox_end_time.get())
                
                if start_seconds < 0:
                    raise ValueError("开始时间不能小于0")
                if end_seconds > self.total_seconds:
                    raise ValueError(f"结束时间不能超过总时长 {self.total_seconds}秒")
                if start_seconds >= end_seconds:
                    raise ValueError("结束时间必须大于开始时间")
            except ValueError as ve:
                if "invalid literal" in str(ve).lower() or "could not convert" in str(ve).lower():
                    raise ValueError("时间必须是有效的数字")
                raise ve
            
            start_frame = int(start_seconds * self.fps)
            # 结束帧+1，使得结束时间对应的那一帧也包含在显示范围内
            # 例如：0-5秒，5.0秒对应的帧也应该显示
            end_frame = int(end_seconds * self.fps) + 1
            duration_frames = end_frame - start_frame
            
            # 默认位置（舞台上方）
            backstage_height = self.stage_height / 8
            default_y = self.stage_height + backstage_height / 2
            default_pos = (0, default_y)
            
            # 创建文本框对象（新版 - 支持每帧不同内容和样式）
            # 初始化每帧的内容数组
            contents_per_frame = ["" for _ in range(self.total_frames)]
            
            # 初始化每帧的字符样式数组
            char_styles_per_frame = [[] for _ in range(self.total_frames)]
            
            # 在开始帧到结束帧之间设置内容和样式
            for frame in range(start_frame, min(end_frame, self.total_frames)):
                contents_per_frame[frame] = content
                # 为这一帧的每个字符设置样式
                frame_char_styles = []
                for char in content:
                    frame_char_styles.append({
                        "font_size": font_size,
                        "color": color
                    })
                char_styles_per_frame[frame] = frame_char_styles
            
            textbox = {
                "name": name,
                "start_frame": start_frame,  # 开始帧
                "duration_frames": duration_frames,  # 持续帧数
                "positions": [default_pos for _ in range(self.total_frames)],
                "keyframes": [start_frame],  # 默认在开始帧有关键帧
                # 每帧的内容和样式
                "contents": contents_per_frame,  # 每帧可以有不同的内容
                "char_styles_per_frame": char_styles_per_frame,  # 每帧每个字符的样式
                # 全局默认样式
                "default_font_size": font_size,
                "default_color": color
            }
            
            # 保存历史记录
            self.save_state_to_history(f"添加文本框 ({name})")
            
            self.textboxes.append(textbox)
            
            # 更新右侧关键帧列表
            self.keyframe_listbox.insert(tk.END, f"文本框: {textbox['name']}")
            
            # 清空输入框并设置默认值
            self.textbox_name_entry.delete(0, tk.END)
            self.textbox_content_entry.delete("1.0", tk.END)
            
            # 更新时间范围默认值为下一个时间段
            next_start = end_seconds
            next_end = min(next_start + 5.0, self.total_seconds)
            self.textbox_start_time.delete(0, tk.END)
            self.textbox_start_time.insert(0, f"{next_start:.1f}")
            self.textbox_end_time.delete(0, tk.END)
            self.textbox_end_time.insert(0, f"{next_end:.1f}")
            
            # 更新显示
            self.update_stage_preview()
            
            # 记录日志
            self.log(f"✓ 添加文本框: {name} ({start_seconds:.1f}秒 → {end_seconds:.1f}秒)", 'success')
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))

    def delete_textbox(self):
        """删除选中的文本框（支持批量删除）"""
        # 优先使用多选列表中的文本框
        textboxes_to_delete = [item for item in self.selected_items if item['type'] == 'textbox']
        
        if textboxes_to_delete:
            # 批量删除模式
            textbox_names = ', '.join([item['item']['name'] for item in textboxes_to_delete])
            
            # 确认删除
            if not messagebox.askyesno("确认", f"确定要删除 {len(textboxes_to_delete)} 个文本框吗？\n{textbox_names}"):
                return
            
            # 保存历史记录
            self.save_state_to_history(f"批量删除文本框 ({len(textboxes_to_delete)}个)")
            
            # 删除文本框
            textboxes_to_delete_objs = [item['item'] for item in textboxes_to_delete]
            self.textboxes = [tb for tb in self.textboxes if tb not in textboxes_to_delete_objs]
            
            # 清空选中列表
            self.selected_items.clear()
            
            # 重建列表显示
            self.keyframe_listbox.delete(0, tk.END)
            for actor in self.actors:
                self.keyframe_listbox.insert(tk.END, f"演员: {actor['name']}")
            for prop in self.props:
                self.keyframe_listbox.insert(tk.END, f"道具: {prop['name']}")
            for textbox in self.textboxes:
                self.keyframe_listbox.insert(tk.END, f"文本框: {textbox['name']}")
            
            # 清空关键帧表格
            for row in self.keyframe_tree.get_children():
                self.keyframe_tree.delete(row)
            
            # 更新舞台预览
            self.update_stage_preview()
            
            # 显示成功提示
            self.log(f"✓ 已删除 {len(textboxes_to_delete)} 个文本框", 'success')
        else:
            # 单个删除模式（从列表框选择）
            selected = self.keyframe_listbox.curselection()
            if not selected:
                messagebox.showwarning("警告", "请先选择一个文本框")
                return
                
            index = selected[0]
            actor_count = len(self.actors)
            prop_count = len(self.props)
            
            if index < actor_count + prop_count:
                messagebox.showwarning("警告", "请选择一个文本框")
                return
                
            textbox_index = index - actor_count - prop_count
            if textbox_index >= len(self.textboxes):
                messagebox.showwarning("警告", "请选择一个文本框")
                return
                
            # 确认删除
            if not messagebox.askyesno("确认", f"确定要删除文本框 {self.textboxes[textbox_index]['name']} 吗？"):
                return
            
            # 保存历史记录
            self.save_state_to_history(f"删除文本框 ({self.textboxes[textbox_index]['name']})")
                
            # 删除文本框
            del self.textboxes[textbox_index]
            
            # 更新列表显示
            self.keyframe_listbox.delete(index)
            
            # 清空关键帧表格
            for row in self.keyframe_tree.get_children():
                self.keyframe_tree.delete(row)
            
            # 更新舞台预览
            self.update_stage_preview()
            
            # 显示成功提示
            self.log("✓ 文本框已删除", 'success')

    def ensure_textbox_arrays(self, textbox, verbose=True):
        """确保文本框的数组存在且大小正确，同时保留现有内容
        
        Args:
            textbox: 文本框对象
            verbose: 是否输出日志
        """
        # 确保contents数组存在且大小正确
        if "contents" not in textbox:
            textbox["contents"] = ["" for _ in range(self.total_frames)]
            if verbose:
                print(f"  ⚠️ 创建新的contents数组")
        elif len(textbox["contents"]) != self.total_frames:
            # 调整数组大小，保留现有内容
            old_contents = textbox["contents"]
            new_contents = ["" for _ in range(self.total_frames)]
            for i in range(min(len(old_contents), self.total_frames)):
                new_contents[i] = old_contents[i]
            textbox["contents"] = new_contents
            if verbose:
                print(f"  ⚠️ 调整contents数组: {len(old_contents)} → {self.total_frames} (已保留内容)")
        
        # 确保char_styles_per_frame数组存在且大小正确
        if "char_styles_per_frame" not in textbox:
            textbox["char_styles_per_frame"] = [[] for _ in range(self.total_frames)]
            if verbose:
                print(f"  ⚠️ 创建新的char_styles_per_frame数组")
        elif len(textbox["char_styles_per_frame"]) != self.total_frames:
            # 调整数组大小，保留现有样式
            old_styles = textbox["char_styles_per_frame"]
            new_styles = [[] for _ in range(self.total_frames)]
            for i in range(min(len(old_styles), self.total_frames)):
                new_styles[i] = old_styles[i]
            textbox["char_styles_per_frame"] = new_styles
            if verbose:
                print(f"  ⚠️ 调整char_styles数组: {len(old_styles)} → {self.total_frames} (已保留样式)")
    
    def ensure_all_textboxes_valid(self):
        """确保所有文本框的数组都有效"""
        for textbox in self.textboxes:
            self.ensure_textbox_arrays(textbox, verbose=False)
    
    def apply_textbox_font_size(self):
        """应用字号到选中文本框的指定文本（从当前帧到剩余时间）"""
        # 检查是否有选中的文本框
        selected_textboxes = [item for item in self.selected_items if item['type'] == 'textbox']
        if not selected_textboxes:
            messagebox.showwarning("警告", "请先选中一个文本框")
            return
        
        try:
            # 获取新字号
            new_font_size = float(self.textbox_font_size.get())
            if new_font_size <= 0:
                raise ValueError("字号必须大于0")
            
            # 使用保存的选中文本（避免焦点转移时丢失选中状态）
            selected_text = self.last_text_selection if hasattr(self, 'last_text_selection') else ""
            
            if selected_text:
                print(f"✓ 使用保存的选中文本: '{selected_text}'")
            else:
                print(f"✓ 没有选中文本，将应用到全部内容")
            
            # 保存历史记录
            self.save_state_to_history(f"修改文本框字号 ({len(selected_textboxes)}个)")
            
            match_count = 0
            # 应用到所有选中的文本框
            for item in selected_textboxes:
                textbox = item['item']
                
                print(f"🔧 应用字号到文本框: {textbox['name']}")
                print(f"  当前帧: {self.current_frame}, total_frames: {self.total_frames}")
                
                # 确保数组存在且大小正确（使用辅助函数）
                self.ensure_textbox_arrays(textbox)
                
                # 计算结束帧
                start_frame = textbox.get("start_frame", 0)
                duration_frames = textbox.get("duration_frames", self.total_frames)
                end_frame = start_frame + duration_frames
                
                print(f"  开始帧: {start_frame}, 持续帧: {duration_frames}, 结束帧: {end_frame}")
                print(f"  应用范围: {self.current_frame} 到 {min(end_frame, self.total_frames)}")
                
                found_in_textbox = False
                # 从当前帧到结束帧应用样式
                for frame in range(self.current_frame, min(end_frame, self.total_frames)):
                    content = textbox["contents"][frame]
                    if not content:
                        print(f"  ⚠️ 帧{frame}内容为空，跳过")
                        continue
                    
                    print(f"  ✓ 处理帧{frame}，内容: '{content}'")
                    
                    # 确保这一帧的字符样式数组存在且长度正确
                    if frame >= len(textbox["char_styles_per_frame"]):
                        # 扩展数组到足够的长度
                        while len(textbox["char_styles_per_frame"]) <= frame:
                            textbox["char_styles_per_frame"].append([])
                    
                    # 检查当前帧的样式数组长度
                    if len(textbox["char_styles_per_frame"][frame]) != len(content):
                        # 需要调整样式数组长度
                        current_styles = textbox["char_styles_per_frame"][frame]
                        default_font_size = textbox.get("default_font_size", 12)
                        default_color = textbox.get("default_color", "black")
                        
                        # 如果样式数组太短，补充默认样式
                        while len(current_styles) < len(content):
                            current_styles.append({
                                "font_size": default_font_size,
                                "color": default_color
                            })
                        # 如果样式数组太长，截断
                        if len(current_styles) > len(content):
                            textbox["char_styles_per_frame"][frame] = current_styles[:len(content)]
                    
                    char_styles = textbox["char_styles_per_frame"][frame]
                    
                    # 如果没有选中文本或没有位置信息，应用到所有字符
                    if not selected_text or not self.last_text_selection_range:
                        for i in range(len(char_styles)):
                            char_styles[i]["font_size"] = new_font_size
                        found_in_textbox = True
                    else:
                        # 使用保存的精确位置索引，只应用到选中的字符
                        selection_range = self.last_text_selection_range
                        if selection_range and isinstance(selection_range, tuple) and len(selection_range) == 2:
                            start_idx = selection_range[0]
                            end_idx = selection_range[1]
                            
                            # 应用字号到选中位置的字符
                            for i in range(start_idx, end_idx):
                                if i < len(char_styles):
                                    char_styles[i]["font_size"] = new_font_size
                            
                            found_in_textbox = True
                            print(f"  应用字号到位置 {start_idx}-{end_idx} 的字符")
                
                if found_in_textbox:
                    match_count += 1
            
            # 更新显示
            self.update_stage_preview()
            
            if not selected_text:
                self.log(f"✓ 已更新字号: 全部文字（持续到剩余时间）", 'success')
            else:
                self.log(f"✓ 已更新字号: \"{selected_text}\" ({match_count}个文本框，持续到剩余时间)", 'success')
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))
    
    def apply_textbox_color(self):
        """应用颜色到选中文本框的指定文本（从当前帧到剩余时间）"""
        # 检查是否有选中的文本框
        selected_textboxes = [item for item in self.selected_items if item['type'] == 'textbox']
        if not selected_textboxes:
            messagebox.showwarning("警告", "请先选中一个文本框")
            return
        
        try:
            # 获取新颜色
            color_map = {**self.color_map, "黑色": "black", "白色": "white"}
            new_color = color_map[self.textbox_color_var.get()]
            
            # 使用保存的选中文本（避免焦点转移时丢失选中状态）
            selected_text = self.last_text_selection if hasattr(self, 'last_text_selection') else ""
            
            if selected_text:
                print(f"✓ 使用保存的选中文本: '{selected_text}'")
            else:
                print(f"✓ 没有选中文本，将应用到全部内容")
            
            # 保存历史记录
            self.save_state_to_history(f"修改文本框颜色 ({len(selected_textboxes)}个)")
            
            match_count = 0
            # 应用到所有选中的文本框
            for item in selected_textboxes:
                textbox = item['item']
                
                print(f"🔧 应用颜色到文本框: {textbox['name']}")
                
                # 确保数组存在且大小正确（使用辅助函数）
                self.ensure_textbox_arrays(textbox)
                
                # 计算结束帧
                start_frame = textbox.get("start_frame", 0)
                duration_frames = textbox.get("duration_frames", self.total_frames)
                end_frame = start_frame + duration_frames
                
                found_in_textbox = False
                # 从当前帧到结束帧应用样式
                for frame in range(self.current_frame, min(end_frame, self.total_frames)):
                    content = textbox["contents"][frame]
                    if not content:
                        continue
                    
                    # 确保这一帧的字符样式数组存在且长度正确
                    if frame >= len(textbox["char_styles_per_frame"]):
                        # 扩展数组到足够的长度
                        while len(textbox["char_styles_per_frame"]) <= frame:
                            textbox["char_styles_per_frame"].append([])
                    
                    # 检查当前帧的样式数组长度
                    if len(textbox["char_styles_per_frame"][frame]) != len(content):
                        # 需要调整样式数组长度
                        current_styles = textbox["char_styles_per_frame"][frame]
                        default_font_size = textbox.get("default_font_size", 12)
                        default_color = textbox.get("default_color", "black")
                        
                        # 如果样式数组太短，补充默认样式
                        while len(current_styles) < len(content):
                            current_styles.append({
                                "font_size": default_font_size,
                                "color": default_color
                            })
                        # 如果样式数组太长，截断
                        if len(current_styles) > len(content):
                            textbox["char_styles_per_frame"][frame] = current_styles[:len(content)]
                    
                    char_styles = textbox["char_styles_per_frame"][frame]
                    
                    # 如果没有选中文本或没有位置信息，应用到所有字符
                    if not selected_text or not self.last_text_selection_range:
                        for i in range(len(char_styles)):
                            char_styles[i]["color"] = new_color
                        found_in_textbox = True
                    else:
                        # 使用保存的精确位置索引，只应用到选中的字符
                        selection_range = self.last_text_selection_range
                        if selection_range and isinstance(selection_range, tuple) and len(selection_range) == 2:
                            start_idx = selection_range[0]
                            end_idx = selection_range[1]
                            
                            # 应用颜色到选中位置的字符
                            for i in range(start_idx, end_idx):
                                if i < len(char_styles):
                                    char_styles[i]["color"] = new_color
                            
                            found_in_textbox = True
                            print(f"  应用颜色到位置 {start_idx}-{end_idx} 的字符")
                
                if found_in_textbox:
                    match_count += 1
            
            # 更新显示
            self.update_stage_preview()
            
            if not selected_text:
                self.log(f"✓ 已更新颜色: 全部文字（持续到剩余时间）", 'success')
            else:
                self.log(f"✓ 已更新颜色: \"{selected_text}\" ({match_count}个文本框，持续到剩余时间)", 'success')
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))
    
    def update_textbox_name(self):
        """更新选中文本框的名称"""
        # 优先从选中对象列表获取文本框
        selected_textboxes = [item for item in self.selected_items if item['type'] == 'textbox']
        
        if not selected_textboxes:
            # 如果没有从选中对象获取到，尝试从列表框获取
            selected = self.keyframe_listbox.curselection()
            if not selected:
                messagebox.showwarning("警告", "请先选择一个文本框")
                return
            
            index = selected[0]
            actor_count = len(self.actors)
            prop_count = len(self.props)
            
            if index < actor_count + prop_count:
                messagebox.showwarning("警告", "请选择一个文本框")
                return
            
            textbox_index = index - actor_count - prop_count
            if textbox_index >= len(self.textboxes):
                messagebox.showwarning("警告", "请选择一个文本框")
                return
            
            textbox = self.textboxes[textbox_index]
        else:
            # 使用选中对象列表中的第一个文本框
            textbox = selected_textboxes[0]['item']
        
        try:
            new_name = self.textbox_name_entry.get()
            if not new_name:
                raise ValueError("名称不能为空")
            
            # 保存历史记录
            old_name = textbox['name']
            self.save_state_to_history(f"修改文本框名称 ({old_name} → {new_name})")
            
            # 更新名称
            textbox['name'] = new_name
            
            # 更新列表显示
            self.keyframe_listbox.delete(0, tk.END)
            for actor in self.actors:
                self.keyframe_listbox.insert(tk.END, f"演员: {actor['name']}")
            for prop in self.props:
                self.keyframe_listbox.insert(tk.END, f"道具: {prop['name']}")
            for tb in self.textboxes:
                self.keyframe_listbox.insert(tk.END, f"文本框: {tb['name']}")
            
            # 重新选中该文本框
            textbox_index = self.textboxes.index(textbox)
            list_index = len(self.actors) + len(self.props) + textbox_index
            self.keyframe_listbox.selection_set(list_index)
            
            # 更新标签
            self.current_item_label.config(text=f"当前编辑: 文本框 {new_name}")
            
            self.log(f"✓ 名称已更新: {old_name} → {new_name}", 'success')
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))
    
    def inherit_text_styles(self, old_content, old_styles, new_content, default_font_size, default_color):
        """智能继承文本样式
        Args:
            old_content: 旧文本内容
            old_styles: 旧字符样式列表
            new_content: 新文本内容
            default_font_size: 默认字号
            default_color: 默认颜色
        Returns:
            新的字符样式列表
        """
        # 如果旧内容为空或没有样式，所有新字符使用默认样式
        if not old_content or not old_styles or len(old_styles) != len(old_content):
            return [{"font_size": default_font_size, "color": default_color} for _ in new_content]
        
        # 如果新内容为空，返回空列表
        if not new_content:
            return []
        
        # 找到公共前缀长度
        prefix_len = 0
        for i in range(min(len(old_content), len(new_content))):
            if old_content[i] == new_content[i]:
                prefix_len += 1
            else:
                break
        
        # 找到公共后缀长度
        suffix_len = 0
        for i in range(1, min(len(old_content) - prefix_len, len(new_content) - prefix_len) + 1):
            if old_content[-i] == new_content[-i]:
                suffix_len += 1
            else:
                break
        
        # 构建新样式列表
        new_styles = []
        
        # 1. 保留前缀部分的样式
        for i in range(prefix_len):
            new_styles.append(old_styles[i].copy())
        
        # 2. 中间新增部分的样式（继承邻近字符）
        middle_len = len(new_content) - prefix_len - suffix_len
        if middle_len > 0:
            # 确定继承来源样式
            if prefix_len > 0:
                # 有前缀，继承前一个字符的样式
                inherit_style = old_styles[prefix_len - 1].copy()
            elif suffix_len > 0 and len(old_content) - suffix_len < len(old_styles):
                # 没有前缀但有后缀，继承后一个字符的样式
                inherit_style = old_styles[len(old_content) - suffix_len].copy()
            else:
                # 都没有，使用默认样式
                inherit_style = {"font_size": default_font_size, "color": default_color}
            
            # 为所有中间字符应用继承的样式
            for _ in range(middle_len):
                new_styles.append(inherit_style.copy())
        
        # 3. 保留后缀部分的样式
        if suffix_len > 0:
            old_suffix_start = len(old_content) - suffix_len
            for i in range(suffix_len):
                new_styles.append(old_styles[old_suffix_start + i].copy())
        
        return new_styles
    
    def update_textbox_content(self):
        """更新选中文本框在当前帧的内容（并应用到剩余时间）"""
        # 优先从选中对象列表获取文本框
        selected_textboxes = [item for item in self.selected_items if item['type'] == 'textbox']
        
        if not selected_textboxes:
            # 如果没有从选中对象获取到，尝试从列表框获取
            selected = self.keyframe_listbox.curselection()
            if not selected:
                messagebox.showwarning("警告", "请先选择一个文本框")
                return
            
            index = selected[0]
            actor_count = len(self.actors)
            prop_count = len(self.props)
            
            if index < actor_count + prop_count:
                messagebox.showwarning("警告", "请选择一个文本框")
                return
            
            textbox_index = index - actor_count - prop_count
            if textbox_index >= len(self.textboxes):
                messagebox.showwarning("警告", "请选择一个文本框")
                return
            
            textbox = self.textboxes[textbox_index]
        else:
            # 使用选中对象列表中的第一个文本框
            textbox = selected_textboxes[0]['item']
        
        try:
            # 使用 "end-1c" 排除末尾自动添加的换行符，保留内容中的换行符
            new_content = self.textbox_content_entry.get("1.0", "end-1c")
            if not new_content.strip():  # 检查是否全是空白字符
                raise ValueError("内容不能为空")
            
            # 保存历史记录
            self.save_state_to_history(f"修改文本框内容（当前帧到剩余时间）")
            
            # 确保数组存在且大小正确（使用辅助函数）
            self.ensure_textbox_arrays(textbox)
            
            # 计算剩余时间（从当前帧到持续时间结束）
            start_frame = textbox.get("start_frame", 0)
            duration_frames = textbox.get("duration_frames", self.total_frames)
            end_frame = start_frame + duration_frames
            
            # 从当前帧到结束帧，设置新内容并智能继承样式
            default_font_size = textbox.get('default_font_size', 12)
            default_color = textbox.get('default_color', 'black')
            
            for frame in range(self.current_frame, min(end_frame, self.total_frames)):
                old_content = textbox["contents"][frame]
                old_styles = textbox["char_styles_per_frame"][frame] if frame < len(textbox["char_styles_per_frame"]) else []
                
                textbox["contents"][frame] = new_content
                
                # 智能继承样式
                new_styles = self.inherit_text_styles(old_content, old_styles, new_content, 
                                                     default_font_size, default_color)
                textbox["char_styles_per_frame"][frame] = new_styles
            
            # 更新显示
            self.update_stage_preview()
            
            frames_updated = min(end_frame, self.total_frames) - self.current_frame
            self.log(f"✓ 内容已更新（从当前帧持续{frames_updated}帧）", 'success')
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))

    def apply_textbox_time_range(self):
        """应用时间范围到选中的文本框（从X秒到Y秒）"""
        # 检查是否有选中的文本框
        selected_textboxes = [item for item in self.selected_items if item['type'] == 'textbox']
        if not selected_textboxes:
            messagebox.showwarning("警告", "请先选中一个文本框")
            return
        
        try:
            # 获取开始和结束时间（秒）
            start_seconds = float(self.textbox_start_time.get())
            end_seconds = float(self.textbox_end_time.get())
            
            print(f"\n📝 应用时间范围:")
            print(f"  从UI读取: 开始={start_seconds:.1f}秒, 结束={end_seconds:.1f}秒")
            
            # 验证时间范围
            if start_seconds < 0:
                raise ValueError("开始时间不能小于0")
            if end_seconds > self.total_seconds:
                raise ValueError(f"结束时间不能超过总时长 {self.total_seconds}秒")
            if start_seconds >= end_seconds:
                raise ValueError("结束时间必须大于开始时间")
            
            # 计算帧数
            start_frame = int(start_seconds * self.fps)
            # 结束帧+1，使得结束时间对应的那一帧也包含在显示范围内
            # 例如：0-5秒，5.0秒对应的帧也应该显示
            end_frame = int(end_seconds * self.fps) + 1
            duration_frames = end_frame - start_frame
            
            print(f"  转换为帧: start_frame={start_frame}, end_frame={end_frame}, duration={duration_frames}")
            print(f"  说明: 显示范围为帧{start_frame}到{end_frame-1}（包含{end_seconds:.1f}秒对应的帧）")
            
            # 保存历史记录
            self.save_state_to_history(f"修改文本框时间范围 ({len(selected_textboxes)}个)")
            
            # 应用到所有选中的文本框
            for item in selected_textboxes:
                textbox = item['item']
                old_start = textbox.get("start_frame", 0)
                old_duration = textbox.get("duration_frames", self.total_frames)
                old_end = old_start + old_duration
                
                # 智能位置处理：根据时间范围变化决定使用哪个位置
                current_position = self.get_item_current_position(textbox)
                
                # 获取旧范围内的位置信息（用于智能位置选择）
                old_start_position = None
                if old_start < len(textbox["positions"]):
                    old_start_position = textbox["positions"][old_start]
                
                # 获取旧范围内最后一个关键帧的位置（用于扩展范围）
                last_keyframe_in_old_range = None
                last_keyframe_position = None
                for kf in reversed(textbox["keyframes"]):
                    if kf < old_end:
                        last_keyframe_in_old_range = kf
                        if kf < len(textbox["positions"]):
                            last_keyframe_position = textbox["positions"][kf]
                        break
                
                # 设置新的时间范围
                textbox["start_frame"] = start_frame
                textbox["duration_frames"] = duration_frames
                
                print(f"  文本框 '{textbox['name']}' 已设置:")
                print(f"    start_frame={textbox['start_frame']}, duration_frames={textbox['duration_frames']}")
                
                # 确保数组存在
                self.ensure_textbox_arrays(textbox, verbose=False)
                
                # 获取当前内容（从旧范围的第一帧获取，作为模板）
                template_content = ""
                template_styles = []
                for frame in range(old_start, min(old_end, self.total_frames)):
                    if frame < len(textbox["contents"]) and textbox["contents"][frame]:
                        template_content = textbox["contents"][frame]
                        template_styles = textbox["char_styles_per_frame"][frame]
                        break
                
                print(f"  获取内容模板: '{template_content[:20]}...' ({len(template_content)}字符)")
                
                # 清除旧范围外的内容（新开始时间之前）
                cleared_before = 0
                for frame in range(old_start, min(start_frame, self.total_frames)):
                    if frame < len(textbox["contents"]):
                        textbox["contents"][frame] = ""
                        textbox["char_styles_per_frame"][frame] = []
                        cleared_before += 1
                if cleared_before > 0:
                    print(f"  清除开始前的内容: {cleared_before}帧 (帧{old_start}-{start_frame-1})")
                
                # 清除新范围外的内容（新结束时间之后）
                # 只在新范围缩短时才清除（end_frame < old_end）
                cleared_after = 0
                if end_frame < old_end:
                    for frame in range(end_frame, min(old_end, self.total_frames)):
                        if frame < len(textbox["contents"]):
                            textbox["contents"][frame] = ""
                            textbox["char_styles_per_frame"][frame] = []
                            cleared_after += 1
                    if cleared_after > 0:
                        print(f"  清除结束后的内容: {cleared_after}帧 (帧{end_frame}-{old_end-1})")
                
                # 关键修复：填充新扩展的时间范围内的内容
                filled_frames = 0
                for frame in range(start_frame, min(end_frame, self.total_frames)):
                    if frame < len(textbox["contents"]):
                        # 如果这一帧没有内容，填充模板内容
                        if not textbox["contents"][frame]:
                            textbox["contents"][frame] = template_content
                            # 深拷贝样式数组，避免引用问题
                            if template_styles:
                                textbox["char_styles_per_frame"][frame] = [style.copy() for style in template_styles]
                            else:
                                textbox["char_styles_per_frame"][frame] = []
                            filled_frames += 1
                
                if filled_frames > 0:
                    print(f"  ✓ 填充扩展范围的内容: {filled_frames}帧")
                    print(f"  新时间范围内容完整: 帧{start_frame}-{end_frame-1} 全部有内容")
                else:
                    print(f"  新时间范围内容已存在，无需填充")
                
                # 智能更新关键帧和位置
                print(f"\n  位置处理分析:")
                print(f"    旧范围: 帧{old_start}-{old_end-1} ({old_start/self.fps:.1f}秒-{(old_end-1)/self.fps:.1f}秒)")
                print(f"    新范围: 帧{start_frame}-{end_frame-1} ({start_frame/self.fps:.1f}秒-{(end_frame-1)/self.fps:.1f}秒)")
                print(f"    当前播放位置: 帧{self.current_frame} ({self.current_frame/self.fps:.1f}秒)")
                
                # 策略1：处理开始帧的关键帧和位置
                if start_frame not in textbox["keyframes"]:
                    textbox["keyframes"].append(start_frame)
                    textbox["keyframes"].sort()
                    print(f"    添加开始关键帧: {start_frame}")
                
                # 决定开始帧使用什么位置
                if start_frame >= old_start and start_frame < old_end:
                    # 开始帧在旧范围内，保持原有位置
                    # 不修改positions[start_frame]，保留原值
                    print(f"    开始帧在旧范围内，保持原有位置")
                else:
                    # 开始帧不在旧范围内（提前了），使用当前位置
                    textbox["positions"][start_frame] = current_position
                    print(f"    开始帧在旧范围外，使用当前位置: {current_position}")
                
                # 策略2：处理扩展范围的位置（时间增加的情况）
                if end_frame > old_end and last_keyframe_position:
                    # 时间范围扩展了，新扩展的部分使用旧范围最后的位置
                    print(f"    时间范围扩展: {old_end-1} → {end_frame-1}")
                    print(f"    扩展范围使用位置: {last_keyframe_position} (来自帧{last_keyframe_in_old_range})")
                    
                    # 在扩展范围的中间添加一个关键帧，使用最后的位置
                    # 这样可以确保扩展部分保持不变
                    if old_end < self.total_frames and old_end not in textbox["keyframes"]:
                        textbox["keyframes"].append(old_end)
                        textbox["keyframes"].sort()
                        textbox["positions"][old_end] = last_keyframe_position
                        print(f"    在扩展起点添加关键帧 {old_end}，位置: {last_keyframe_position}")
                
                # 策略3：清除新范围外的关键帧
                # 移除不在新范围内的关键帧
                textbox["keyframes"] = [kf for kf in textbox["keyframes"] if start_frame <= kf < end_frame]
                print(f"    保留的关键帧: {textbox['keyframes']}")
            
            # 更新显示
            self.update_stage_preview()
            
            # 重要：更新UI显示，确保时间范围输入框显示正确的值
            # （因为可能有舍入误差，需要用实际存储的值更新UI）
            if len(selected_textboxes) == 1:
                # 单选时，强制更新样式UI以显示实际的时间范围
                textbox = selected_textboxes[0]['item']
                self.update_textbox_current_style_ui(textbox, force_update_time=True)
                
                # 显示实际应用的值（考虑帧率舍入）
                actual_start = textbox["start_frame"] / self.fps
                actual_end = (textbox["start_frame"] + textbox["duration_frames"]) / self.fps
                print(f"✓ 时间范围应用成功:")
                print(f"  输入: {start_seconds:.1f}秒 → {end_seconds:.1f}秒")
                print(f"  实际: {actual_start:.1f}秒 → {actual_end:.1f}秒")
                print(f"  帧数: {textbox['start_frame']} → {textbox['start_frame'] + textbox['duration_frames']}")
                
                # 验证UI是否真的被更新了
                ui_start = self.textbox_start_time.get()
                ui_end = self.textbox_end_time.get()
                print(f"\n🔍 验证UI状态:")
                print(f"  开始时间输入框当前值: {ui_start}")
                print(f"  结束时间输入框当前值: {ui_end}")
                print(f"  期望值: {actual_start:.1f} → {actual_end:.1f}")
                
                # 如果不匹配，发出警告
                try:
                    if abs(float(ui_start) - actual_start) > 0.01 or abs(float(ui_end) - actual_end) > 0.01:
                        print(f"⚠️ 警告：UI显示值与实际值不匹配！")
                        print(f"  正在强制刷新UI...")
                        # 再次强制更新
                        self.textbox_start_time.delete(0, tk.END)
                        self.textbox_start_time.insert(0, f"{actual_start:.1f}")
                        self.textbox_end_time.delete(0, tk.END)
                        self.textbox_end_time.insert(0, f"{actual_end:.1f}")
                        print(f"  ✓ UI已强制刷新")
                except:
                    pass
            
            self.log(f"✓ 已更新时间范围: {start_seconds:.1f}秒 → {end_seconds:.1f}秒", 'success')
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))
    
    def _fill_current_time(self, entry_widget):
        """双击时间输入框时自动填充当前时间"""
        entry_widget.delete(0, tk.END)
        entry_widget.insert(0, f"{self.current_second:.1f}")
        entry_widget.select_range(0, tk.END)
        return "break"  # 防止默认的双击选择行为
    
    def apply_textbox_all_styles(self):
        """合并应用文本框的字号、颜色和时间范围"""
        selected_textboxes = [item for item in self.selected_items if item['type'] == 'textbox']
        if not selected_textboxes:
            messagebox.showwarning("警告", "请先选中一个文本框")
            return
        
        try:
            # 应用字号
            self.apply_textbox_font_size()
            # 应用颜色
            self.apply_textbox_color()
            # 应用时间范围
            self.apply_textbox_time_range()
        except Exception as e:
            messagebox.showerror("错误", f"应用样式失败：{str(e)}")
    
    def update_textbox_current_style_ui(self, textbox, force_update_time=False):
        """更新文本框样式UI显示（显示当前帧的内容和样式）
        
        Args:
            textbox: 文本框对象
            force_update_time: 是否强制更新时间范围（默认False，只在选择不同文本框时更新）
        """
        # 检查是否是同一个文本框
        is_same_textbox = (self.last_selected_textbox_for_ui is textbox)
        
        # 获取当前帧的内容
        contents_array = textbox.get("contents", [])
        if self.current_frame < len(contents_array):
            current_content = contents_array[self.current_frame]
        else:
            current_content = ""
        
        # 获取当前帧的字符样式
        char_styles_array = textbox.get("char_styles_per_frame", [])
        if self.current_frame < len(char_styles_array) and len(char_styles_array[self.current_frame]) > 0:
            first_char_style = char_styles_array[self.current_frame][0]
            default_font_size = first_char_style.get("font_size", 12)
            default_color = first_char_style.get("color", "black")
        else:
            default_font_size = textbox.get("default_font_size", 12)
            default_color = textbox.get("default_color", "black")
        
        # 更新UI
        self.textbox_font_size.delete(0, tk.END)
        self.textbox_font_size.insert(0, str(int(default_font_size)))
        
        # 更新时间范围（开始时间和结束时间）
        # 只在选择不同文本框时更新，避免覆盖用户正在编辑的值
        if not is_same_textbox or force_update_time:
            start_frame = textbox.get("start_frame", 0)
            duration_frames = textbox.get("duration_frames", int(5 * self.fps))
            end_frame = start_frame + duration_frames
            
            start_seconds = start_frame / self.fps
            end_seconds = end_frame / self.fps
            
            print(f"🔄 更新时间范围UI (force={force_update_time}, is_same={is_same_textbox}):")
            print(f"  start_frame={start_frame}, duration_frames={duration_frames}, end_frame={end_frame}")
            print(f"  start_seconds={start_seconds:.1f}, end_seconds={end_seconds:.1f}")
            
            self.textbox_start_time.delete(0, tk.END)
            self.textbox_start_time.insert(0, f"{start_seconds:.1f}")
            print(f"  ✓ 开始时间输入框已更新: {self.textbox_start_time.get()}")
            
            self.textbox_end_time.delete(0, tk.END)
            self.textbox_end_time.insert(0, f"{end_seconds:.1f}")
            print(f"  ✓ 结束时间输入框已更新: {self.textbox_end_time.get()}")
            
            # 更新跟踪变量
            self.last_selected_textbox_for_ui = textbox
            
            time_info = f"时间范围: {start_seconds:.1f}秒 → {end_seconds:.1f}秒"
        else:
            time_info = "时间范围未更新（避免覆盖用户输入）"
        
        # 颜色映射（反向查找中文名称）
        color_reverse_map = {
            "black": "黑色", "red": "红色", "blue": "蓝色", 
            "green": "绿色", "purple": "紫色", "orange": "橙色", "white": "白色"
        }
        color_name = color_reverse_map.get(default_color, "黑色")
        self.textbox_color_var.set(color_name)
        
        print(f"✓ 样式UI已更新，{time_info}，内容：'{current_content}'")


    def update_intermediate_frames(self, item):
        """更新两个关键帧之间的中间帧位置，使用线性插值确保匀速移动"""
        if len(item["keyframes"]) < 2:
            return
            
        # 按时间排序关键帧
        sorted_frames = sorted(item["keyframes"])
        
        # 更新每对关键帧之间的中间帧
        for i in range(len(sorted_frames) - 1):
            start_frame = sorted_frames[i]
            end_frame = sorted_frames[i + 1]
            start_pos = item["positions"][start_frame]
            end_pos = item["positions"][end_frame]
            
            # 计算总距离
            total_frames = end_frame - start_frame
            if total_frames <= 1:
                continue
                
            # 计算每帧的移动距离
            dx = (end_pos[0] - start_pos[0]) / total_frames
            dy = (end_pos[1] - start_pos[1]) / total_frames
            
            # 使用线性插值更新中间帧位置
            for frame in range(start_frame + 1, end_frame):
                progress = frame - start_frame
                x = start_pos[0] + dx * progress
                y = start_pos[1] + dy * progress
                item["positions"][frame] = (x, y)

    def update_intermediate_rotations(self, item):
        """更新两个旋转关键帧之间的中间帧旋转角度，使用线性插值
        
        支持多圈旋转：
        - 正数角度表示顺时针旋转
        - 负数角度表示逆时针旋转
        - 角度可以超过360度（如720度表示顺时针旋转2圈）
        - 插值按完整角度差值计算，不走最短路径
        """
        # 确保存在旋转数组和旋转关键帧
        if "rotation_keyframes" not in item or "rotations" not in item:
            return
        
        if len(item["rotation_keyframes"]) == 0:
            return
        
        # 按时间排序关键帧
        sorted_frames = sorted(item["rotation_keyframes"])
        
        print(f"🔄 更新旋转插值: {item.get('name', '未命名')} 关键帧={sorted_frames}")
        
        # 处理第一个关键帧之前的帧（如果第一个关键帧不是第0帧）
        first_keyframe = sorted_frames[0]
        if first_keyframe > 0:
            # 从0度插值到第一个关键帧
            first_rotation = item["rotations"][first_keyframe]
            total_frames = first_keyframe
            d_rotation = first_rotation / total_frames
            print(f"  帧0(0.0°) → 帧{first_keyframe}({first_rotation:.1f}°): 每帧变化{d_rotation:.2f}°")
            for frame in range(0, first_keyframe):
                rotation = d_rotation * frame
                item["rotations"][frame] = rotation  # 不归一化
        
        # 更新每对关键帧之间的中间帧
        for i in range(len(sorted_frames) - 1):
            start_frame = sorted_frames[i]
            end_frame = sorted_frames[i + 1]
            start_rotation = item["rotations"][start_frame]
            end_rotation = item["rotations"][end_frame]
            
            # 计算总帧数
            total_frames = end_frame - start_frame
            if total_frames <= 1:
                continue
                
            # 直接计算角度差值（不选择最短路径，支持多圈旋转）
            rotation_diff = end_rotation - start_rotation
            d_rotation = rotation_diff / total_frames
            
            # 显示旋转信息
            if abs(rotation_diff) > 360:
                circles = abs(rotation_diff) / 360
                direction = "顺时针" if rotation_diff > 0 else "逆时针"
                print(f"  帧{start_frame}({start_rotation:.1f}°) → 帧{end_frame}({end_rotation:.1f}°): {direction}旋转{circles:.1f}圈, 每帧变化{d_rotation:.2f}°")
            else:
                print(f"  帧{start_frame}({start_rotation:.1f}°) → 帧{end_frame}({end_rotation:.1f}°): 每帧变化{d_rotation:.2f}°")
            
            # 使用线性插值更新中间帧旋转角度（保留完整角度值）
            for frame in range(start_frame + 1, end_frame):
                progress = frame - start_frame
                rotation = start_rotation + d_rotation * progress
                item["rotations"][frame] = rotation  # 不归一化，保留原始角度
        
        # 重要：将最后一个关键帧的旋转角度延续到后续所有帧
        last_keyframe = sorted_frames[-1]
        last_rotation = item["rotations"][last_keyframe]
        for frame in range(last_keyframe + 1, len(item["rotations"])):
            item["rotations"][frame] = last_rotation
        
        print(f"  ✓ 插值完成，最后关键帧{last_keyframe}({last_rotation:.1f}°)延续到结束")

    def get_item_current_position(self, item):
        """获取元素的当前位置（考虑关键帧插值和临时覆盖）"""
        # 获取基于关键帧的位置
        if item["keyframes"]:
            prev_frame = max([f for f in item["keyframes"] if f <= self.current_frame], default=None)
            next_frame = min([f for f in item["keyframes"] if f > self.current_frame], default=None)
            
            if prev_frame is not None:
                if next_frame is not None:
                    pos = item["positions"][self.current_frame]
                else:
                    pos = item["positions"][prev_frame]
            else:
                pos = item["positions"][0]
        else:
            pos = item["positions"][0]
        
        # 检查是否有临时位置覆盖
        item_id = self.get_element_id(item)
        if item_id in self.temp_position_overrides:
            pos = self.temp_position_overrides[item_id]
        
        return pos
    
    def is_point_in_item(self, x, y, item, item_type):
        """检查点击位置是否在元素内"""
        pos = self.get_item_current_position(item)
        
        if item_type == "actor":
            if item["shape"] == "circle":
                # size是直径，计算半径
                radius = item["size"] / 2
                return ((x - pos[0])**2 + (y - pos[1])**2) <= radius**2
            elif item["shape"] == "square":
                return (abs(x - pos[0]) <= item["size"]/2 and 
                        abs(y - pos[1]) <= item["size"]/2)
            elif item["shape"] == "triangle":
                return (abs(x - pos[0]) <= item["size"] and 
                        abs(y - pos[1]) <= item["size"])
        elif item_type == "prop":
            if item["shape"] == "rectangle":
                return (abs(x - pos[0]) <= item["width"]/2 and 
                        abs(y - pos[1]) <= item["height"]/2)
            elif item["shape"] == "circle":
                return ((x - pos[0])**2 + (y - pos[1])**2) <= (item["width"]/2)**2
            elif item["shape"] == "triangle":
                return (abs(x - pos[0]) <= item["width"]/2 and 
                        abs(y - pos[1]) <= item["height"]/2)
        elif item_type == "textbox":
            # 文本框使用矩形碰撞检测（基于当前帧的内容和样式）
            # 首先检查是否在显示时间范围内
            start_frame = item.get("start_frame", 0)
            duration_frames = item.get("duration_frames", self.total_frames)
            end_frame = start_frame + duration_frames
            
            # 只在时间范围内才能点击
            if not (start_frame <= self.current_frame < end_frame):
                return False
            
            # 获取当前帧的内容
            contents_array = item.get("contents", [])
            if self.current_frame < len(contents_array):
                content = contents_array[self.current_frame]
            else:
                content = ""
            
            if not content:
                return False  # 没有内容，无法点击
            
            # 获取当前帧的字符样式
            char_styles_array = item.get("char_styles_per_frame", [])
            if self.current_frame < len(char_styles_array):
                char_styles = char_styles_array[self.current_frame]
            else:
                char_styles = []
            
            # 如果有字符样式，使用平均字号估算；否则使用默认字号
            if char_styles and len(char_styles) == len(content):
                avg_font_size = sum(s.get("font_size", 12) for s in char_styles) / len(char_styles)
                max_font_size = max(s.get("font_size", 12) for s in char_styles)
            else:
                default_font_size = item.get("default_font_size", 12)
                avg_font_size = default_font_size
                max_font_size = default_font_size
            
            # 估算文本宽度和高度（用于点击检测）
            # 使用与渲染时相同的宽度计算方式，确保碰撞检测准确
            # 字符宽度系数0.05与渲染时保持一致，并增加容错范围
            text_width = len(content) * avg_font_size * 0.05
            # 增加与舞台尺寸成比例的容错范围（舞台越大，容错范围越大）
            stage_scale = (self.stage_width + self.stage_height) / 35  # 标准舞台(20+15=35)为基准
            text_width += 1.5 * stage_scale  # 宽度容错
            
            # 高度基于缩放后的字号计算，确保在不同缩放下都能准确点击
            # 获取actual_view_scale，如果不存在则使用1.0
            view_scale = getattr(self, 'actual_view_scale', 1.0)
            # 基于字号和缩放计算高度
            scaled_height = max_font_size * view_scale * 0.15
            # 增加与舞台尺寸成比例的容错范围
            scaled_height += 1.5 * stage_scale  # 高度容错
            
            # 调试输出点击检测范围（仅在点击时输出）
            # print(f"🎯 文本框点击范围 | 宽={text_width:.2f} | 高={scaled_height:.2f} | 舞台缩放={stage_scale:.2f}")
            
            return (abs(x - pos[0]) <= text_width/2 and 
                    abs(y - pos[1]) <= scaled_height/2)
        return False
    
    def on_mouse_press(self, event):
        """处理鼠标按下事件"""
        if event.inaxes != self.ax:
            return
            
        # 获取鼠标点击位置
        x, y = event.xdata, event.ydata
        
        # 右键（button==3）或中键（button==2）用于平移视图
        if event.button == 3 or event.button == 2:
            # 双击右键重置视图
            if event.dblclick:
                self.view_center = None
                self.zoom_scale = 1.0
                self.update_stage_preview()
                print("🔄 视图已重置到默认状态")
                self.log("🔄 视图已重置", 'info')
                return
            
            # 单击右键开始平移
            self.pan_active = True
            self.pan_start = (x, y)
            # 保存当前视图中心
            xlim = self.ax.get_xlim()
            ylim = self.ax.get_ylim()
            if self.view_center is None:
                self.view_center = ((xlim[0] + xlim[1]) / 2, (ylim[0] + ylim[1]) / 2)
            print(f"🖐️ 开始平移视图，起始位置: ({x:.2f}, {y:.2f})")
            return  # 平移模式下不处理对象拖动
        
        # 检测是否按住Ctrl键（多选模式）
        ctrl_pressed = event.key == 'control' if hasattr(event, 'key') and event.key else False
        
        # 记录当前是否有选择（用于后续判断是否需要刷新）
        had_selection = len(self.selected_items) > 0
        
        # 查找点击的对象 - 收集所有被点击的对象，循环选择重叠对象
        clicked_candidates = []  # 存储所有被点击的候选对象
        
        # 检查演员 - 按照添加顺序（索引从大到小，后添加的优先）
        for i, actor in enumerate(self.actors):
            if self.is_point_in_item(x, y, actor, "actor"):
                clicked_candidates.append({
                    'item': actor,
                    'type': 'actor',
                    'index': i,
                    'list_order': len(self.actors) - i  # 后添加的对象order值更大
                })
        
        # 检查道具 - 按照添加顺序
        for i, prop in enumerate(self.props):
            if self.is_point_in_item(x, y, prop, "prop"):
                clicked_candidates.append({
                    'item': prop,
                    'type': 'prop',
                    'index': i,
                    'list_order': len(self.props) - i
                })
        
        # 检查文本框 - 按照添加顺序
        for i, textbox in enumerate(self.textboxes):
            if self.is_point_in_item(x, y, textbox, "textbox"):
                clicked_candidates.append({
                    'item': textbox,
                    'type': 'textbox',
                    'index': i,
                    'list_order': len(self.textboxes) - i
                })
        
        # 检查是否在同一位置点击（循环选择）
        same_position = False
        if self.last_click_pos is not None:
            dx = abs(x - self.last_click_pos[0])
            dy = abs(y - self.last_click_pos[1])
            distance = (dx**2 + dy**2)**0.5
            same_position = distance < self.click_position_tolerance
        
        # 选择要使用的对象
        clicked_item = None
        clicked_type = None
        clicked_index = None
        
        if clicked_candidates:
            # 如果位置改变了，或者候选列表改变了，重新构建候选列表
            if not same_position or len(clicked_candidates) != len(self.overlap_candidates):
                # 按照list_order从大到小排序（后添加的在前面，模拟图层顺序）
                clicked_candidates.sort(key=lambda c: c['list_order'], reverse=True)
                self.overlap_candidates = clicked_candidates
                
                # 检查候选列表中是否有已经选中的对象
                # 如果有，优先使用那个对象（保持选中状态）
                selected_candidate_index = -1
                for i, candidate in enumerate(self.overlap_candidates):
                    if any(item['item'] is candidate['item'] for item in self.selected_items):
                        selected_candidate_index = i
                        break
                
                if selected_candidate_index >= 0:
                    # 有已选中的对象在候选列表中，使用它
                    self.overlap_current_index = selected_candidate_index
                    print(f"🎯 保持选中的对象: {self.overlap_candidates[selected_candidate_index]['item']['name']}")
                else:
                    # 没有已选中的对象，使用第一个候选
                    self.overlap_current_index = 0
                
                self.last_click_pos = (x, y)
                print(f"🆕 新位置，检测到 {len(clicked_candidates)} 个对象")
            # 注意：在同一位置重复点击时，不在这里切换对象，而是在 on_mouse_release 时切换
            
            # 选择当前索引的对象（不改变索引）
            if self.overlap_candidates:
                current = self.overlap_candidates[self.overlap_current_index]
                clicked_item = current['item']
                clicked_type = current['type']
                clicked_index = current['index']
                
                # 显示选择信息
                if len(self.overlap_candidates) > 1:
                    print(f"🎯 当前: {clicked_item['name']} ({self.overlap_current_index + 1}/{len(self.overlap_candidates)})")
                else:
                    print(f"🎯 选中: {clicked_item['name']}")
        
        # 如果点击到了对象
        if clicked_item is not None:
            pos = self.get_item_current_position(clicked_item)
            item_id = self.get_element_id(clicked_item)
            
            # 清除临时位置覆盖
            if item_id in self.temp_position_overrides:
                self.temp_position_overrides.pop(item_id)
            
            # 将当前帧的临时关键帧转为正式关键帧
            self.convert_temp_keyframe_to_permanent(clicked_item, self.current_frame)
            
            # 检查是否已经在选中列表中
            already_selected = any(
                item['item'] is clicked_item 
                for item in self.selected_items
            )
            
            # Ctrl多选模式
            if ctrl_pressed:
                if already_selected:
                    # 如果已选中，标记为待取消（在释放鼠标时根据是否拖动来决定是否取消）
                    # 这样可以避免在拖动多选对象时误取消
                    self.pending_deselect_item = clicked_item
                    print(f"🔶 Ctrl+点击已选中对象: {clicked_item['name']} (待确认：拖动or取消)")
                    # 继续执行下面的代码，设置拖动状态
                    # 如果发生拖动，on_mouse_move会清除pending_deselect_item
                    # 如果没有拖动（位置不变），on_mouse_release会执行取消操作
                else:
                    # 添加到选中列表
                    self.selected_items.append({
                        'item': clicked_item,
                        'type': clicked_type,
                        'index': clicked_index,
                        'start_pos': pos
                    })
                    print(f"✅ 添加选中: {clicked_item['name']}")
            else:
                # 非Ctrl模式
                if already_selected:
                    # 点击已选中的对象，保持所有选择，准备拖动
                    # 不清空选择，这样可以直接拖动多个对象而无需按Ctrl
                    print(f"🔵 点击已选中对象: {clicked_item['name']} (准备拖动 {len(self.selected_items)} 个对象)")
                else:
                    # 点击未选中的对象，清空之前的选择，只选中当前对象
                    self.selected_items.clear()
                    self.selected_items.append({
                        'item': clicked_item,
                        'type': clicked_type,
                        'index': clicked_index,
                        'start_pos': pos
                    })
                    # 如果选中的不是文本框，清空文本框UI跟踪
                    if clicked_type != 'textbox':
                        self.last_selected_textbox_for_ui = None
                    print(f"🔵 单选: {clicked_item['name']}")
            
            # 如果有选中的对象，开始拖动
            if len(self.selected_items) > 0:
                # 在开始拖动前，更新所有选中对象的起始位置为当前实际位置
                # 这样可以确保即使对象之前被移动过，也能正确计算相对位移
                for selected in self.selected_items:
                    current_pos = self.get_item_current_position(selected['item'])
                    selected['start_pos'] = current_pos
                
                self.dragging = True
                self.drag_item = clicked_item  # 保持兼容性
                self.drag_type = clicked_type
                self.drag_index = clicked_index
                self.drag_offset = (x - pos[0], y - pos[1])
                self.drag_start_pos = pos
                self.drag_end_pos = pos  # 初始化为相同位置，只有真正移动时才会改变
                self.multi_select_start_mouse_pos = (x, y)
                
                # 更新列表框选择
                if not ctrl_pressed:
                    self.keyframe_listbox.selection_clear(0, tk.END)
                
                # 显示选中状态
                for selected in self.selected_items:
                    list_index = selected['index']
                    if selected['type'] == 'prop':
                        list_index += len(self.actors)
                    elif selected['type'] == 'textbox':
                        list_index += len(self.actors) + len(self.props)
                    self.keyframe_listbox.selection_set(list_index)
                
                # 更新关键帧表格（只在单选时调用，多选时不调用以保留选中状态）
                if len(self.selected_items) == 1:
                    self.on_keyframe_list_select(None)
                
                # 显示多选提示
                if len(self.selected_items) > 1:
                    names = ', '.join([item['item']['name'] for item in self.selected_items])
                    self.log(f"🔘 已选中 {len(self.selected_items)} 个对象: {names}", 'info')
                    print(f"🔘 多选模式: {len(self.selected_items)} 个对象")
                
                # 如果选中的是文本框，更新当前帧样式显示
                if clicked_type == 'textbox':
                    self.update_textbox_current_style_ui(clicked_item)
            
            # 刷新显示以显示选中高亮
            self.update_stage_preview()
        else:
            # 点击空白处
            self.pending_deselect_item = None  # 清除待取消标志
            
            # 重置循环选择状态
            self.last_click_pos = None
            self.overlap_candidates = []
            self.overlap_current_index = 0
            
            if ctrl_pressed:
                # Ctrl模式下点击空白处，开始矩形框选
                self.rect_selecting = True
                self.rect_select_start = (x, y)
                self.rect_select_end = (x, y)
                print(f"🔲 开始矩形框选，起点: ({x:.2f}, {y:.2f})")
            else:
                # 非Ctrl模式下，清空所有选择
                if had_selection:
                    print(f"❌ 点击空白处，清空 {len(self.selected_items)} 个选中对象")
                    self.selected_items.clear()
                    # 清空列表框选择
                    self.keyframe_listbox.selection_clear(0, tk.END)
                    # 清空上次选中的文本框跟踪
                    self.last_selected_textbox_for_ui = None
                    self.update_stage_preview()
                    self.log("已清空选择", 'info')

    def on_mouse_move(self, event):
        """处理鼠标移动事件"""
        # 记录鼠标位置（用于粘贴功能）
        if event.inaxes == self.ax and event.xdata is not None and event.ydata is not None:
            self.last_mouse_pos = (event.xdata, event.ydata)
        
        # 处理矩形框选
        if self.rect_selecting:
            if event.inaxes == self.ax and event.xdata is not None and event.ydata is not None:
                # 更新矩形框的结束点
                self.rect_select_end = (event.xdata, event.ydata)
                # 刷新显示以绘制矩形框
                self.update_stage_preview()
            return
        
        # 处理视图平移
        if self.pan_active and self.pan_start is not None:
            if event.inaxes != self.ax or event.xdata is None or event.ydata is None:
                return
            
            # 计算鼠标移动的距离
            dx = event.xdata - self.pan_start[0]
            dy = event.ydata - self.pan_start[1]
            
            # 更新视图中心（反向移动，因为是拖动背景）
            current_center = self.view_center if self.view_center is not None else (0, self.stage_height / 2)
            self.view_center = (current_center[0] - dx, current_center[1] - dy)
            
            # 更新起始位置为当前位置（相对于新的视图中心）
            self.pan_start = (event.xdata, event.ydata)
            
            # 刷新显示
            self.update_stage_preview()
            return
        
        # 处理对象拖动
        if not self.dragging:
            return
        
        # 类型检查：确保拖动相关对象不为None
        if self.drag_item is None or self.drag_offset is None:
            return
        
        # 获取鼠标位置 - 即使鼠标移出画布区域也继续拖动
        # 如果鼠标在画布内，使用实际位置；如果在画布外，暂停拖动更新
        if event.inaxes == self.ax and event.xdata is not None and event.ydata is not None:
            x = event.xdata
            y = event.ydata
        else:
            # 鼠标在画布外，暂停拖动更新但保持拖动状态
            # 这样当鼠标移回画布时可以继续拖动
            return
        
        # 计算从起始位置移动的距离
        if self.drag_start_pos:
            move_distance = ((x - self.drag_start_pos[0])**2 + (y - self.drag_start_pos[1])**2)**0.5
        else:
            move_distance = 0
        
        # 如果是第一次拖动（还未保存过历史），保存历史记录
        # 只有当移动距离超过阈值时才认为是真正的拖动
        if (not hasattr(self, '_drag_history_saved') or not self._drag_history_saved) and move_distance >= 0.5:
            # 如果有待取消标志，说明用户选择了拖动而不是取消，清除标志
            if self.pending_deselect_item is not None:
                print(f"🔄 拖动距离 {move_distance:.3f} ≥ 0.5，清除待取消标志")
                self.pending_deselect_item = None
            
            if len(self.selected_items) > 1:
                names = ', '.join([item['item']['name'] for item in self.selected_items])
                self.save_state_to_history(f"拖动多个对象 ({names})")
            else:
                self.save_state_to_history(f"拖动对象 ({self.drag_item['name']})")
            self._drag_history_saved = True
        
        # 如果是多选模式，移动所有选中的对象
        if len(self.selected_items) > 1 and self.multi_select_start_mouse_pos is not None:
            # 计算鼠标移动的距离
            dx = x - self.multi_select_start_mouse_pos[0]
            dy = y - self.multi_select_start_mouse_pos[1]
            
            # 清空对齐辅助线
            self.align_guides.clear()
            
            # 检测第一个对象的智能吸附（用于整组对齐）
            first_item = self.selected_items[0]['item']
            first_start_pos = self.selected_items[0]['start_pos']
            first_new_x = first_start_pos[0] + dx
            first_new_y = first_start_pos[1] + dy
            
            # 应用智能吸附
            if self.smart_align_enabled.get():
                snapped_x, snapped_y, guides = self.check_smart_align_snap(first_item, first_new_x, first_new_y)
                # 计算吸附后的偏移调整
                snap_dx = snapped_x - first_new_x
                snap_dy = snapped_y - first_new_y
                dx += snap_dx
                dy += snap_dy
                self.align_guides = guides
            
            # 移动所有选中的对象
            for selected in self.selected_items:
                item = selected['item']
                start_pos = selected['start_pos']
                
                # 计算新位置（保持相对位置不变）
                new_x = start_pos[0] + dx
                new_y = start_pos[1] + dy
                
                # 更新位置
                item["positions"][self.current_frame] = (new_x, new_y)
                
                # 如果当前帧不是关键帧，添加为关键帧
                if self.current_frame not in item["keyframes"]:
                    item["keyframes"].append(self.current_frame)
                    item["keyframes"].sort()
            
            # 更新 drag_end_pos 为第一个对象的新位置
            self.drag_end_pos = (first_new_x, first_new_y)
        else:
            # 单选模式，只移动一个对象
            # 根据偏移量计算元素的新位置
            new_x = x - self.drag_offset[0]
            new_y = y - self.drag_offset[1]
            
            # 清空对齐辅助线
            self.align_guides.clear()
            
            # 应用智能吸附（如果启用）
            if self.smart_align_enabled.get():
                snapped_x, snapped_y, guides = self.check_smart_align_snap(self.drag_item, new_x, new_y)
                new_x = snapped_x
                new_y = snapped_y
                self.align_guides = guides
            
            # 更新位置
            self.drag_item["positions"][self.current_frame] = (new_x, new_y)
            
            # 更新 drag_end_pos
            self.drag_end_pos = (new_x, new_y)
            
            # 如果当前帧不是关键帧，添加为关键帧
            if self.current_frame not in self.drag_item["keyframes"]:
                self.drag_item["keyframes"].append(self.current_frame)
                self.drag_item["keyframes"].sort()
        
        # 更新关键帧表格（只在单选时调用，多选时不调用以保留选中状态）
        if len(self.selected_items) == 1:
            self.on_keyframe_list_select(None)
        
        # 更新显示
        self.update_stage_preview()
        
    def on_mouse_release(self, event):
        """处理鼠标释放事件"""
        # 结束矩形框选
        if self.rect_selecting:
            self.rect_selecting = False
            
            if self.rect_select_start and self.rect_select_end:
                # 计算矩形框的边界
                x1, y1 = self.rect_select_start
                x2, y2 = self.rect_select_end
                min_x, max_x = min(x1, x2), max(x1, x2)
                min_y, max_y = min(y1, y2), max(y1, y2)
                
                print(f"🔲 矩形框选结束: ({min_x:.2f}, {min_y:.2f}) → ({max_x:.2f}, {max_y:.2f})")
                
                # 查找框内的所有对象
                selected_count = 0
                
                # 检查演员
                for i, actor in enumerate(self.actors):
                    pos = self.get_item_current_position(actor)
                    # 检查对象中心点是否在矩形框内
                    if min_x <= pos[0] <= max_x and min_y <= pos[1] <= max_y:
                        # 检查是否已经选中
                        already_selected = any(item['item'] is actor for item in self.selected_items)
                        if not already_selected:
                            self.selected_items.append({
                                'item': actor,
                                'type': 'actor',
                                'index': i,
                                'start_pos': pos
                            })
                            selected_count += 1
                
                # 检查道具
                for i, prop in enumerate(self.props):
                    pos = self.get_item_current_position(prop)
                    # 检查对象中心点是否在矩形框内
                    if min_x <= pos[0] <= max_x and min_y <= pos[1] <= max_y:
                        # 检查是否已经选中
                        already_selected = any(item['item'] is prop for item in self.selected_items)
                        if not already_selected:
                            self.selected_items.append({
                                'item': prop,
                                'type': 'prop',
                                'index': i,
                                'start_pos': pos
                            })
                            selected_count += 1
                
                # 检查文本框
                for i, textbox in enumerate(self.textboxes):
                    pos = self.get_item_current_position(textbox)
                    # 检查对象中心点是否在矩形框内
                    if min_x <= pos[0] <= max_x and min_y <= pos[1] <= max_y:
                        # 检查是否已经选中
                        already_selected = any(item['item'] is textbox for item in self.selected_items)
                        if not already_selected:
                            self.selected_items.append({
                                'item': textbox,
                                'type': 'textbox',
                                'index': i,
                                'start_pos': pos
                            })
                            selected_count += 1
                
                # 更新列表框选择
                self.keyframe_listbox.selection_clear(0, tk.END)
                for selected in self.selected_items:
                    list_index = selected['index']
                    if selected['type'] == 'prop':
                        list_index += len(self.actors)
                    elif selected['type'] == 'textbox':
                        list_index += len(self.actors) + len(self.props)
                    self.keyframe_listbox.selection_set(list_index)
                
                # 显示结果
                if selected_count > 0:
                    names = ', '.join([item['item']['name'] for item in self.selected_items[-selected_count:]])
                    print(f"✅ 框选添加了 {selected_count} 个对象: {names}")
                    if len(self.selected_items) > 0:
                        all_names = ', '.join([item['item']['name'] for item in self.selected_items])
                        self.log(f"🔲 已选中 {len(self.selected_items)} 个对象: {all_names}", 'info')
                else:
                    print(f"⚠️ 框内没有对象")
            
            # 清除框选状态
            self.rect_select_start = None
            self.rect_select_end = None
            
            # 刷新显示
            self.update_stage_preview()
            return
        
        # 结束视图平移
        if self.pan_active:
            self.pan_active = False
            self.pan_start = None
            print(f"🖐️ 视图平移结束，新中心: ({self.view_center[0]:.2f}, {self.view_center[1]:.2f})" if self.view_center else "🖐️ 视图平移结束")
            return
        
        if not self.dragging:
            # 清除待取消标志
            self.pending_deselect_item = None
            return
            
        # 获取最终位置 - 如果 drag_end_pos 没有被 on_mouse_move 更新，才使用当前鼠标位置
        # 这样可以避免点击时因坐标微小差异导致误判为拖动
        if event.inaxes == self.ax:
            # 只有在移动过程中才更新 drag_end_pos
            # 如果没有移动，drag_end_pos 保持为初始值（等于 drag_start_pos）
            pass  # drag_end_pos 已经在 on_mouse_move 中更新了
        else:
            # 如果释放时鼠标在预览区域外，将元素限制在预览区域边缘
            # 获取当前预览区域的边界
            x_min, x_max = self.ax.get_xlim()
            y_min, y_max = self.ax.get_ylim()
            
            # 获取鼠标在窗口中的位置（像素坐标）
            if hasattr(event, 'x') and hasattr(event, 'y'):
                # 将像素坐标转换为数据坐标的近似值
                # 使用拖拽开始时的位置作为参考
                if self.drag_start_pos is not None:
                    last_x, last_y = self.drag_start_pos
                else:
                    # 如果没有起始位置，使用舞台中心
                    last_x, last_y = 0, self.stage_height / 2
                
                # 简单的边界限制：保持在预览区域内
                x = max(x_min, min(x_max, last_x))
                y = max(y_min, min(y_max, last_y))
                
                # 如果能够获取到更精确的鼠标位置，进一步优化
                try:
                    # 尝试获取相对于图形的位置
                    inv = self.ax.transData.inverted()
                    x_pixel, y_pixel = event.x, event.y
                    
                    # 获取图形在窗口中的位置
                    bbox = self.ax.bbox
                    if x_pixel < bbox.x0:  # 左边界外
                        x = x_min + 0.5  # 留一点边距
                    elif x_pixel > bbox.x1:  # 右边界外
                        x = x_max - 0.5
                    
                    if y_pixel < bbox.y0:  # 下边界外
                        y = y_min + 0.5
                    elif y_pixel > bbox.y1:  # 上边界外
                        y = y_max - 0.5
                except:
                    # 如果转换失败，使用保守的边界限制
                    pass
                    
            else:
                # 如果无法获取鼠标位置，使用拖拽起始位置
                if self.drag_start_pos is not None:
                    x, y = self.drag_start_pos
                else:
                    # 如果没有起始位置，使用舞台中心
                    x, y = 0, self.stage_height / 2
                # 确保在边界内
                x = max(x_min, min(x_max, x))
                y = max(y_min, min(y_max, y))
            
            self.drag_end_pos = (x, y)
            print(f"元素在预览区域外释放，限制到边缘位置: ({x:.2f}, {y:.2f})")
            
        # 计算拖动距离
        if self.drag_start_pos and self.drag_end_pos:
            drag_distance = ((self.drag_end_pos[0] - self.drag_start_pos[0])**2 + 
                           (self.drag_end_pos[1] - self.drag_start_pos[1])**2)**0.5
        else:
            drag_distance = 0
        
        # 增加调试信息 - 显示拖动距离
        print(f"📏 拖动距离: {drag_distance:.3f} (阈值: 0.5)")
        if self.pending_deselect_item is not None:
            print(f"   待取消对象: {self.pending_deselect_item['name']}")
        
        # 如果位置没有变化或移动距离很小（< 0.5，视为点击而非拖动）
        # 提高阈值到 0.5 以减少鼠标轻微抖动造成的误判
        if drag_distance < 0.5:
            # 先处理待取消选中的对象（Ctrl+点击已选中对象但未拖动）
            pending_deselect_handled = False
            if self.pending_deselect_item is not None:
                if len(self.selected_items) > 1:
                    # 不是最后一个对象，可以取消选中
                    item_to_remove = self.pending_deselect_item
                    self.selected_items = [
                        item for item in self.selected_items 
                        if item['item'] is not item_to_remove
                    ]
                    print(f"❌ 取消选中: {item_to_remove['name']}")
                    self.log(f"取消选中: {item_to_remove['name']}", 'info')
                    # 更新列表框选择
                    self.keyframe_listbox.selection_clear(0, tk.END)
                    for selected in self.selected_items:
                        list_index = selected['index']
                        if selected['type'] == 'prop':
                            list_index += len(self.actors)
                        elif selected['type'] == 'textbox':
                            list_index += len(self.actors) + len(self.props)
                        self.keyframe_listbox.selection_set(list_index)
                    self.update_stage_preview()
                    pending_deselect_handled = True
                else:
                    # 是最后一个对象，不取消选中
                    print(f"⚠️ 最后一个对象，保持选中: {self.pending_deselect_item['name']}")
                
                self.pending_deselect_item = None
            
            # 处理重叠对象的循环选择：只有在没有处理 pending_deselect 时才循环切换
            if (not pending_deselect_handled and
                len(self.overlap_candidates) > 1 and 
                self.last_click_pos is not None and 
                event.xdata is not None and event.ydata is not None):
                # 检查是否在同一位置
                dx = abs(event.xdata - self.last_click_pos[0])
                dy = abs(event.ydata - self.last_click_pos[1])
                distance = (dx**2 + dy**2)**0.5
                if distance < self.click_position_tolerance:
                    # 切换到下一个对象
                    old_index = self.overlap_current_index
                    self.overlap_current_index = (self.overlap_current_index + 1) % len(self.overlap_candidates)
                    
                    # 获取新选中的对象
                    new_current = self.overlap_candidates[self.overlap_current_index]
                    new_item = new_current['item']
                    new_type = new_current['type']
                    new_index = new_current['index']
                    new_pos = self.get_item_current_position(new_item)
                    
                    # 更新选中列表（替换为新对象）
                    self.selected_items.clear()
                    self.selected_items.append({
                        'item': new_item,
                        'type': new_type,
                        'index': new_index,
                        'start_pos': new_pos
                    })
                    
                    # 更新列表框选择
                    self.keyframe_listbox.selection_clear(0, tk.END)
                    list_index = new_index
                    if new_type == 'prop':
                        list_index += len(self.actors)
                    elif new_type == 'textbox':
                        list_index += len(self.actors) + len(self.props)
                    self.keyframe_listbox.selection_set(list_index)
                    
                    # 更新关键帧表格
                    self.on_keyframe_list_select(None)
                    
                    # 如果是文本框，更新样式UI
                    if new_type == 'textbox':
                        self.update_textbox_current_style_ui(new_item)
                    
                    # 显示切换信息
                    print(f"🔄 循环切换: {old_index + 1}→{self.overlap_current_index + 1}/{len(self.overlap_candidates)}")
                    print(f"🎯 现在选中: {new_item['name']} ({self.overlap_current_index + 1}/{len(self.overlap_candidates)})")
                    # 显示所有候选对象列表
                    print(f"   候选对象列表:")
                    for i, c in enumerate(self.overlap_candidates):
                        marker = "👉" if i == self.overlap_current_index else "  "
                        print(f"   {marker} {i+1}. {c['item']['name']} ({c['type']})")
                    
                    # 更新舞台预览以显示新选中的对象
                    self.update_stage_preview()
                    
                    self.log(f"🔄 切换选中: {new_item['name']} ({self.overlap_current_index + 1}/{len(self.overlap_candidates)})", 'info')
            
            # 重置拖动状态
            self.dragging = False
            self.drag_item = None
            self.drag_type = None
            self.drag_index = None
            self.drag_start_pos = None
            self.drag_end_pos = None
            self._drag_history_saved = False  # 重置拖动历史保存标志
            return
            
        # 保存最后拖动的项目和位置
        self.last_dragged_item = self.drag_item
        self.last_dragged_pos = self.drag_end_pos
        
        # 更新所有移动对象的中间帧插值（修复文本框跳跃问题）
        if len(self.selected_items) > 1:
            # 多选模式：更新所有选中对象的插值
            for selected in self.selected_items:
                item = selected['item']
                self.update_intermediate_frames(item)
        elif self.drag_item:
            # 单选模式：更新单个对象的插值
            self.update_intermediate_frames(self.drag_item)
        
        # 记录拖动操作到日志
        if len(self.selected_items) > 1:
            names = ', '.join([item['item']['name'] for item in self.selected_items])
            self.log(f"✓ 移动了 {len(self.selected_items)} 个对象: {names}", 'success')
        elif self.drag_item and self.drag_end_pos:
            self.log(f"拖动对象: {self.drag_item['name']} → ({self.drag_end_pos[0]:.1f}, {self.drag_end_pos[1]:.1f})", 'info')
        
        # 启用插入关键帧按钮
        self.insert_keyframe_btn.config(state='normal')
        
        # 如果有待取消标志但发生了拖动，清除标志（用户是想拖动）
        if self.pending_deselect_item is not None:
            print(f"🔄 发生了拖动(距离≥0.5)，取消待取消操作: {self.pending_deselect_item['name']}")
            self.pending_deselect_item = None
        
        # 重置拖动状态
        self.dragging = False
        self.drag_item = None
        self.drag_type = None
        self.drag_index = None
        self.drag_start_pos = None
        self.drag_end_pos = None
        self.multi_select_start_mouse_pos = None
        self._drag_history_saved = False  # 重置拖动历史保存标志
        
        # 清空对齐辅助线
        self.align_guides.clear()
        
        # 不清空 selected_items，保持选中状态以便继续操作
    
    def on_mouse_scroll(self, event):
        """处理鼠标滚轮事件 - 缩放舞台预览"""
        # event.button: 'up' 表示向上滚动（放大），'down' 表示向下滚动（缩小）
        if event.button == 'up':
            # 放大：增加缩放比例
            new_zoom = self.zoom_scale * 1.1
        elif event.button == 'down':
            # 缩小：减少缩放比例
            new_zoom = self.zoom_scale / 1.1
        else:
            return  # 其他按钮事件不处理
        
        # 限制缩放范围
        new_zoom = max(self.min_zoom, min(self.max_zoom, new_zoom))
        
        # 如果缩放比例没有变化，直接返回
        if abs(new_zoom - self.zoom_scale) < 0.001:
            return
        
        # 更新缩放比例
        old_zoom = self.zoom_scale
        self.zoom_scale = new_zoom
        
        # 更新舞台预览
        self.update_stage_preview()
        
        # 显示缩放信息
        zoom_percent = int(self.zoom_scale * 100)
        print(f"🔍 缩放: {zoom_percent}% (从 {int(old_zoom*100)}% 到 {zoom_percent}%)")
        
        # 在日志窗口显示缩放比例（可选）
        if zoom_percent % 10 == 0 or zoom_percent in [30, 300]:  # 只在整10%或极值时显示
            self.log(f"🔍 缩放: {zoom_percent}%", 'info')

    def on_key_press(self, event):
        """处理键盘按键事件"""
        # matplotlib 在不同平台上的 Ctrl 键处理方式可能不同
        # 支持多种格式: 'ctrl+c', 'control+c', 以及单独的 'c' + ctrl 修饰符
        key = event.key.lower() if event.key else ''
        
        # 检测 Ctrl+C (复制)
        if key in ['ctrl+c', 'control+c'] or (key == 'c' and event.key and 'ctrl' in event.key.lower()):
            self.copy_selected_items()
            print(f"🔑 检测到快捷键: Ctrl+C")
        # 检测 Ctrl+V (粘贴)
        elif key in ['ctrl+v', 'control+v'] or (key == 'v' and event.key and 'ctrl' in event.key.lower()):
            self.paste_items()
            print(f"🔑 检测到快捷键: Ctrl+V")
           ��测 Delete 键 (删除)
        elif key in ['delete', 'del']:
            self.delete_selected_items()
            print(f"🔑 检测到快捷键: Delete")

    def copy_selected_items(self):
        """复制选中的对象到剪贴板"""
        if not self.selected_items:
            self.log("没有选中的对象", 'warning')
            return
        
        # 深拷贝选中的对象
        import copy
        self.clipboard = []
        
        for selected in self.selected_items:
            item = selected['item']
            item_type = selected['type']
            
            # 创建对象的深拷贝
            item_copy = copy.deepcopy(item)
            
            self.clipboard.append({
                'type': item_type,
                'item': item_copy
            })
        
        # 显示复制信息
        names = ', '.join([item['item']['name'] for item in self.selected_items])
        self.log(f"📋 已复制 {len(self.selected_items)} 个对象: {names}", 'success')
        print(f"📋 复制成功: {len(self.selected_items)} 个对象")

    def paste_items(self):
        """在鼠标位置粘贴对象"""
        if not self.clipboard:
            self.log("剪贴板为空", 'warning')
            return
        
        import copy
        
        # 保存历史记录
        self.save_state_to_history(f"粘贴 {len(self.clipboard)} 个对象")
        
        # 计算粘贴位置 - 使用当前鼠标位置
        paste_x, paste_y = self.last_mouse_pos
        
        # 如果有多个对象，计算它们的中心点
        if len(self.clipboard) > 1:
            # 获取原始对象在当前帧的位置
            original_positions = []
            for clip_item in self.clipboard:
                item = clip_item['item']
                current_pos = self.get_item_current_position(item)
                original_positions.append(current_pos)
            
            # 计算原始对象的中心
            center_x = sum(pos[0] for pos in original_positions) / len(original_positions)
            center_y = sum(pos[1] for pos in original_positions) / len(original_positions)
        else:
            # 单个对象，直接使用其位置
            item = self.clipboard[0]['item']
            center_x, center_y = self.get_item_current_position(item)
        
        # 计算偏移量
        offset_x = paste_x - center_x
        offset_y = paste_y - center_y
        
        pasted_items = []
        
        for clip_item in self.clipboard:
            item = clip_item['item']
            item_type = clip_item['type']
            
            # 创建新的对象副本
            new_item = copy.deepcopy(item)
            
            # 生成新的名称（避免重名）
            original_name = new_item['name']
            new_name = self.generate_unique_name(original_name, item_type)
            new_item['name'] = new_name
            
            # 调整所有帧的位置（应用偏移量）
            for i in range(len(new_item['positions'])):
                old_pos = new_item['positions'][i]
                new_item['positions'][i] = (old_pos[0] + offset_x, old_pos[1] + offset_y)
            
            # 添加到对应的列表
            list_index = 0  # 默认值
            if item_type == 'actor':
                self.actors.append(new_item)
                list_index = len(self.actors) - 1
                self.keyframe_listbox.insert(list_index, f"演员: {new_name}")
            elif item_type == 'prop':
                self.props.append(new_item)
                list_index = len(self.actors) + len(self.props) - 1
                self.keyframe_listbox.insert(list_index, f"道具: {new_name}")
            elif item_type == 'textbox':
                self.textboxes.append(new_item)
                list_index = len(self.actors) + len(self.props) + len(self.textboxes) - 1
                self.keyframe_listbox.insert(list_index, f"文本: {new_name}")
            
            pasted_items.append({
                'item': new_item,
                'type': item_type,
                'index': list_index,
                'name': new_name
            })
        
        # 清空当前选择，选中新粘贴的对象
        self.selected_items.clear()
        self.selected_items = pasted_items
        
        # 更新列表框选择
        self.keyframe_listbox.selection_clear(0, tk.END)
        for selected in self.selected_items:
            list_index = selected['index']
            self.keyframe_listbox.selection_set(list_index)
        
        # 更新显示
        self.update_stage_preview()
        
        # 显示粘贴信息
        names = ', '.join([item['name'] for item in pasted_items])
        self.log(f"✓ 已粘贴 {len(pasted_items)} 个对象: {names}", 'success')
        print(f"✓ 粘贴成功: {len(pasted_items)} 个对象在 ({paste_x:.1f}, {paste_y:.1f})")

    def generate_unique_name(self, original_name, item_type):
        """生成唯一的对象名称"""
        # 获取对应类型的所有现有名称
        if item_type == 'actor':
            existing_names = [actor['name'] for actor in self.actors]
        elif item_type == 'prop':
            existing_names = [prop['name'] for prop in self.props]
        elif item_type == 'textbox':
            existing_names = [textbox['name'] for textbox in self.textboxes]
        else:
            existing_names = []
        
        # 如果原始名称不存在，直接使用
        if original_name not in existing_names:
            return original_name
        
        # 否则，添加数字后缀
        counter = 1
        while True:
            new_name = f"{original_name}_副本{counter}"
            if new_name not in existing_names:
                return new_name
            counter += 1

    def delete_selected_items(self):
        """删除选中的对象（支持批量删除和混合类型删除）"""
        if not self.selected_items:
            self.log("没有选中的对象", 'warning')
            print("⚠️ 没有选中的对象")
            return
        
        # 分类选中的对象
        actors_to_delete = [item for item in self.selected_items if item['type'] == 'actor']
        props_to_delete = [item for item in self.selected_items if item['type'] == 'prop']
        textboxes_to_delete = [item for item in self.selected_items if item['type'] == 'textbox']
        
        # 统计信息
        total_count = len(self.selected_items)
        actor_count = len(actors_to_delete)
        prop_count = len(props_to_delete)
        textbox_count = len(textboxes_to_delete)
        
        # 构建确认信息
        type_info = []
        if actor_count > 0:
            type_info.append(f"{actor_count}个演员")
        if prop_count > 0:
            type_info.append(f"{prop_count}个道具")
        if textbox_count > 0:
            type_info.append(f"{textbox_count}个文本框")
        
        type_str = "、".join(type_info)
        
        # 列出所有要删除的对象名称
        all_names = [item['item']['name'] for item in self.selected_items]
        names_str = ', '.join(all_names)
        
        # 确认删除
        if not messagebox.askyesno("确认删除", 
            f"确定要删除 {total_count} 个对象吗？\n\n包括：{type_str}\n\n对象：{names_str}"):
            print("❌ 用户取消删除")
            return
        
        # 保存历史记录
        self.save_state_to_history(f"批量删除对象 ({total_count}个: {type_str})")
        
        # 删除演员
        if actors_to_delete:
            actors_to_delete_objs = [item['item'] for item in actors_to_delete]
            self.actors = [actor for actor in self.actors if actor not in actors_to_delete_objs]
            print(f"🗑️ 删除了 {len(actors_to_delete)} 个演员")
        
        # 删除道具
        if props_to_delete:
            props_to_delete_objs = [item['item'] for item in props_to_delete]
            self.props = [prop for prop in self.props if prop not in props_to_delete_objs]
            print(f"🗑️ 删除了 {len(props_to_delete)} 个道具")
        
        # 删除文本框
        if textboxes_to_delete:
            textboxes_to_delete_objs = [item['item'] for item in textboxes_to_delete]
            self.textboxes = [tb for tb in self.textboxes if tb not in textboxes_to_delete_objs]
            print(f"🗑️ 删除了 {len(textboxes_to_delete)} 个文本框")
        
        # 清空选中列表
        self.selected_items.clear()
        
        # 重建列表显示
        self.keyframe_listbox.delete(0, tk.END)
        for actor in self.actors:
            self.keyframe_listbox.insert(tk.END, f"演员: {actor['name']}")
        for prop in self.props:
            self.keyframe_listbox.insert(tk.END, f"道具: {prop['name']}")
        for textbox in self.textboxes:
            self.keyframe_listbox.insert(tk.END, f"文本框: {textbox['name']}")
        
        # 清空关键帧表格
        for row in self.keyframe_tree.get_children():
            self.keyframe_tree.delete(row)
        
        # 清空最后选中的文本框跟踪
        self.last_selected_textbox_for_ui = None
        
        # 更新舞台预览
        self.update_stage_preview()
        
        # 显示成功提示
        self.log(f"🗑️ 已删除 {total_count} 个对象 ({type_str}): {names_str}", 'success')
        print(f"✓ 删除成功: {total_count} 个对象")

    def insert_keyframe(self):
        """插入关键帧"""
        if not self.last_dragged_item:
            return
            
        # 清除该元素的临时位置覆盖（用户手动移动后确认位置）
        element_id = self.get_element_id(self.last_dragged_item)
        if element_id in self.temp_position_overrides:
            self.temp_position_overrides.pop(element_id)
            
        # 添加关键帧
        if self.current_frame not in self.last_dragged_item["keyframes"]:
            # 保存历史记录
            self.save_state_to_history(f"插入关键帧 ({self.last_dragged_item['name']} @ {int(self.current_second)}秒)")
            
            # 更新位置
            self.last_dragged_item["positions"][self.current_frame] = self.last_dragged_pos
            self.last_dragged_item["keyframes"].append(self.current_frame)
            
            # 更新中间帧
            self.update_intermediate_frames(self.last_dragged_item)
            
            # 更新显示
            self.update_stage_preview()
            
            # 显示成功提示
            self.log(f"✓ 在第 {int(self.current_second)}秒 插入关键帧", 'success')
            
        # 禁用插入关键帧按钮
        self.insert_keyframe_btn.config(state='disabled')
        
        # 清除最后拖动的状态
        self.last_dragged_item = None
        self.last_dragged_pos = None


    def batch_insert_keyframe(self):
        """为所有选中的演员和道具在当前帧插入关键帧，保持它们的当前位置"""
        # 检查是否有选中的对象
        if not self.selected_items:
            self.log("⚠️ 请先选中至少一个对象", 'warning')
            return
        
        # 保存历史记录
        self.save_state_to_history(f"批量插入关键帧 (@ {int(self.current_second)}秒)")
        
        count = 0
        
        # 只为选中的对象添加关键帧
        for selected in self.selected_items:
            item = selected['item']
            item_type = selected['type']
            
            # 跳过文本框类型（如果有的话）
            if item_type not in ['actor', 'prop']:
                continue
            
            if self.current_frame not in item["keyframes"]:
                # 获取对象的当前实际位置（与update_stage_preview中的逻辑一致）
                if item["keyframes"]:  # 如果有关键帧
                    # 找到当前帧之前和之后的关键帧
                    prev_frame = max([f for f in item["keyframes"] if f <= self.current_frame], default=None)
                    next_frame = min([f for f in item["keyframes"] if f > self.current_frame], default=None)
                    
                    if prev_frame is not None:
                        if next_frame is not None:
                            # 在两个关键帧之间进行插值
                            current_pos = item["positions"][self.current_frame]
                        else:
                            # 使用最后一个关键帧的位置
                            current_pos = item["positions"][prev_frame]
                    else:
                        # 使用初始位置
                        current_pos = item["positions"][0]
                else:
                    # 没有关键帧时使用初始位置
                    current_pos = item["positions"][0]
                
                # 在当前帧插入关键帧，位置为当前实际位置
                item["positions"][self.current_frame] = current_pos
                item["keyframes"].append(self.current_frame)
                item["keyframes"].sort()
                self.update_intermediate_frames(item)
                count += 1
                print(f"为{item_type == 'actor' and '演员' or '道具'} {item['name']} 在第 {self.current_frame} 帧插入关键帧，位置: {current_pos}")
        
        # 更新显示
        self.update_stage_preview()
        self.on_keyframe_list_select(None)
        
        # 显示操作结果
        current_time = int(self.current_second)
        if count > 0:
            self.log(f"✓ 批量插入完成: 已为 {count} 个选中元素在第 {current_time}秒 插入关键帧", 'success')
        else:
            self.log(f"所有选中元素在第 {current_time}秒 都已有关键帧", 'info')
    
    def check_smart_align_snap(self, obj, new_x, new_y):
        """检查智能对齐吸附
        
        Args:
            obj: 正在拖动的对象
            new_x, new_y: 拖动到的新位置
            
        Returns:
            (snapped_x, snapped_y, guides): 吸附后的位置和辅助线列表
        """
        if not self.smart_align_enabled.get():
            return new_x, new_y, []
        
        snapped_x = new_x
        snapped_y = new_y
        guides = []
        
        # 收集所有其他对象（不包括正在拖动的对象）
        other_objects = []
        for actor in self.actors:
            if actor is not obj:
                pos = self.get_item_current_position(actor)
                other_objects.append(('actor', actor, pos))
        for prop in self.props:
            if prop is not obj:
                pos = self.get_item_current_position(prop)
                other_objects.append(('prop', prop, pos))
        
        # 检测X方向的吸附
        min_x_dist = float('inf')
        snap_x = None
        x_guide = None
        
        for obj_type, other_obj, other_pos in other_objects:
            # 检查中心对齐
            dist = abs(new_x - other_pos[0])
            if dist < self.snap_threshold and dist < min_x_dist:
                min_x_dist = dist
                snap_x = other_pos[0]
                # 绘制垂直辅助线
                x_guide = (other_pos[0], -10, other_pos[0], self.stage_height + 10, 'vertical')
        
        # 检测Y方向的吸附
        min_y_dist = float('inf')
        snap_y = None
        y_guide = None
        
        for obj_type, other_obj, other_pos in other_objects:
            # 检查中心对齐
            dist = abs(new_y - other_pos[1])
            if dist < self.snap_threshold and dist < min_y_dist:
                min_y_dist = dist
                snap_y = other_pos[1]
                # 绘制水平辅助线
                y_guide = (-self.stage_width, other_pos[1], self.stage_width, other_pos[1], 'horizontal')
        
        # 应用吸附
        if snap_x is not None:
            snapped_x = snap_x
            if x_guide:
                guides.append(x_guide)
        
        if snap_y is not None:
            snapped_y = snap_y
            if y_guide:
                guides.append(y_guide)
        
        return snapped_x, snapped_y, guides
    
    def quick_align(self, align_mode):
        """快速对齐到指定方式
        
        Args:
            align_mode: 对齐方式 (center/left/right/top/bottom)
        """
        if not self.selected_items:
            self.log("⚠️ 请先选中要对齐的对象", 'warning')
            return
        
        # 收集选中对象的当前位置
        positions = []
        for selected_item in self.selected_items:
            obj = selected_item['item']
            pos = self.get_item_current_position(obj)
            positions.append((obj, pos))
        
        # 计算对齐参数
        target_x = None
        target_y = None
        align_desc = ""
        
        if align_mode == "center":
            target_x = 0
            target_y = self.stage_height / 2
            align_desc = "舞台中心"
        elif align_mode == "left":
            target_x = min(pos[1][0] for pos in positions)
            align_desc = f"左对齐"
        elif align_mode == "right":
            target_x = max(pos[1][0] for pos in positions)
            align_desc = f"右对齐"
        elif align_mode == "top":
            target_y = max(pos[1][1] for pos in positions)
            align_desc = f"上对齐"
        elif align_mode == "bottom":
            target_y = min(pos[1][1] for pos in positions)
            align_desc = f"下对齐"
        else:
            return
        
        # 保存历史记录
        self.save_state_to_history(f"对齐对象 ({align_desc})")
        
        # 应用对齐
        aligned_count = 0
        for obj, old_pos in positions:
            new_x = target_x if target_x is not None else old_pos[0]
            new_y = target_y if target_y is not None else old_pos[1]
            new_pos = (new_x, new_y)
            
            if old_pos != new_pos:
                obj["positions"][self.current_frame] = new_pos
                
                # 如果当前帧不是关键帧，添加为关键帧
                if self.current_frame not in obj["keyframes"]:
                    obj["keyframes"].append(self.current_frame)
                    obj["keyframes"].sort()
                    self.update_intermediate_frames(obj)
                
                aligned_count += 1
        
        if aligned_count > 0:
            # 更新选中对象的start_pos为新位置，避免下次拖动时跳回
            for selected_item in self.selected_items:
                obj = selected_item['item']
                new_pos = self.get_item_current_position(obj)
                selected_item['start_pos'] = new_pos
            
            self.update_stage_preview()
            self.on_keyframe_list_select(None)
            self.log(f"✓ 已{align_desc} {aligned_count} 个对象", 'success')
            
            # 确保画布获得焦点，以便后续的鼠标事件能正常处理
            self.canvas.get_tk_widget().focus_set()
            print(f"✅ 对齐完成，选中状态保持: {len(self.selected_items)} 个对象")
    
    def apply_actor_name(self):
        """应用演员新名称"""
        try:
            # 检查是否有选中的演员
            selected_actors = [item for item in self.selected_items if item['type'] == 'actor']
            
            if not selected_actors:
                messagebox.showwarning("警告", "请先选中一个演员")
                return
            
            if len(selected_actors) > 1:
                messagebox.showwarning("警告", "只能修改一个演员的名称")
                return
            
            # 获取新名称
            new_name = self.actor_name_entry.get().strip()
            if not new_name:
                raise ValueError("演员名称不能为空")
            
            # 获取选中的演员
            selected_item = selected_actors[0]
            actor = selected_item['item']
            actor_index = selected_item['index']
            old_name = actor['name']
            
            # 更新演员名称
            actor['name'] = new_name
            
            # 保存历史记录
            self.save_state_to_history(f"修改演员名称: {old_name} → {new_name}")
            
            # 更新关键帧列表显示
            self.keyframe_listbox.delete(actor_index)
            self.keyframe_listbox.insert(actor_index, f"演员: {new_name}")
            self.keyframe_listbox.selection_set(actor_index)
            
            # 更新当前编辑标签
            self.current_item_label.config(text=f"当前编辑: 演员 {new_name}")
            
            # 更新显示
            self.update_stage_preview()
            
            # 记录日志
            self.log(f"✓ 演员名称已更新: {old_name} → {new_name}", 'success')
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))
    
    def apply_unified_font_size(self):
        """统一的字号应用（根据选中的对象类型调用相应函数）"""
        selected_actors = [item for item in self.selected_items if item['type'] == 'actor']
        selected_props = [item for item in self.selected_items if item['type'] == 'prop']
        
        if not selected_actors and not selected_props:
            messagebox.showwarning("警告", "请先选中演员或道具")
            return
        
        try:
            new_font_size = float(self.unified_font_size.get())
            if new_font_size <= 0:
                raise ValueError("字号必须大于0")
            
            # 保存历史记录
            total_count = len(selected_actors) + len(selected_props)
            self.save_state_to_history(f"修改名称字号 ({total_count}个)")
            
            # 应用到演员
            for item in selected_actors:
                actor = item['item']
                if "name_char_styles_per_frame" not in actor:
                    actor["name_char_styles_per_frame"] = []
                while len(actor["name_char_styles_per_frame"]) < self.total_frames:
                    actor["name_char_styles_per_frame"].append([])
                
                for frame in range(self.current_frame, self.total_frames):
                    name = actor["name"]
                    if not name:
                        continue
                    frame_styles = actor["name_char_styles_per_frame"][frame]
                    default_color = actor.get("color", "blue")
                    while len(frame_styles) < len(name):
                        frame_styles.append({"font_size": actor.get("font_size", 10), "color": default_color})
                    if len(frame_styles) > len(name):
                        actor["name_char_styles_per_frame"][frame] = frame_styles[:len(name)]
                        frame_styles = actor["name_char_styles_per_frame"][frame]
                    for i in range(len(frame_styles)):
                        frame_styles[i]["font_size"] = new_font_size
            
            # 应用到道具
            for item in selected_props:
                prop = item['item']
                if "name_char_styles_per_frame" not in prop:
                    prop["name_char_styles_per_frame"] = []
                while len(prop["name_char_styles_per_frame"]) < self.total_frames:
                    prop["name_char_styles_per_frame"].append([])
                
                for frame in range(self.current_frame, self.total_frames):
                    name = prop["name"]
                    if not name:
                        continue
                    frame_styles = prop["name_char_styles_per_frame"][frame]
                    default_color = prop.get("color", "red")
                    while len(frame_styles) < len(name):
                        frame_styles.append({"font_size": prop.get("font_size", 10), "color": default_color})
                    if len(frame_styles) > len(name):
                        prop["name_char_styles_per_frame"][frame] = frame_styles[:len(name)]
                        frame_styles = prop["name_char_styles_per_frame"][frame]
                    for i in range(len(frame_styles)):
                        frame_styles[i]["font_size"] = new_font_size
            
            self.update_stage_preview()
            self.log(f"✓ 已更新 {total_count} 个对象的名称字号", 'success')
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))
    
    def apply_unified_color(self):
        """统一的颜色应用（根据选中的对象类型调用相应函数）"""
        selected_actors = [item for item in self.selected_items if item['type'] == 'actor']
        selected_props = [item for item in self.selected_items if item['type'] == 'prop']
        
        if not selected_actors and not selected_props:
            messagebox.showwarning("警告", "请先选中演员或道具")
            return
        
        try:
            color_map = {**self.color_map, "黑色": "black", "白色": "white"}
            new_color = color_map[self.unified_color_var.get()]
            
            # 保存历史记录
            total_count = len(selected_actors) + len(selected_props)
            self.save_state_to_history(f"修改名称颜色 ({total_count}个)")
            
            # 应用到演员
            for item in selected_actors:
                actor = item['item']
                if "name_char_styles_per_frame" not in actor:
                    actor["name_char_styles_per_frame"] = []
                while len(actor["name_char_styles_per_frame"]) < self.total_frames:
                    actor["name_char_styles_per_frame"].append([])
                
                for frame in range(self.current_frame, self.total_frames):
                    name = actor["name"]
                    if not name:
                        continue
                    frame_styles = actor["name_char_styles_per_frame"][frame]
                    default_color = actor.get("color", "blue")
                    while len(frame_styles) < len(name):
                        frame_styles.append({"font_size": actor.get("font_size", 10), "color": default_color})
                    if len(frame_styles) > len(name):
                        actor["name_char_styles_per_frame"][frame] = frame_styles[:len(name)]
                        frame_styles = actor["name_char_styles_per_frame"][frame]
                    for i in range(len(frame_styles)):
                        frame_styles[i]["color"] = new_color
            
            # 应用到道具
            for item in selected_props:
                prop = item['item']
                if "name_char_styles_per_frame" not in prop:
                    prop["name_char_styles_per_frame"] = []
                while len(prop["name_char_styles_per_frame"]) < self.total_frames:
                    prop["name_char_styles_per_frame"].append([])
                
                for frame in range(self.current_frame, self.total_frames):
                    name = prop["name"]
                    if not name:
                        continue
                    frame_styles = prop["name_char_styles_per_frame"][frame]
                    default_color = prop.get("color", "red")
                    while len(frame_styles) < len(name):
                        frame_styles.append({"font_size": prop.get("font_size", 10), "color": default_color})
                    if len(frame_styles) > len(name):
                        prop["name_char_styles_per_frame"][frame] = frame_styles[:len(name)]
                        frame_styles = prop["name_char_styles_per_frame"][frame]
                    for i in range(len(frame_styles)):
                        frame_styles[i]["color"] = new_color
            
            self.update_stage_preview()
            self.log(f"✓ 已更新 {total_count} 个对象的名称颜色", 'success')
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))
    
    def apply_unified_style(self):
        """统一的样式应用（同时应用字号和颜色）"""
        selected_actors = [item for item in self.selected_items if item['type'] == 'actor']
        selected_props = [item for item in self.selected_items if item['type'] == 'prop']
        
        if not selected_actors and not selected_props:
            messagebox.showwarning("警告", "请先选中演员或道具")
            return
        
        try:
            new_font_size = float(self.unified_font_size.get())
            if new_font_size <= 0:
                raise ValueError("字号必须大于0")
            
            color_map = {**self.color_map, "黑色": "black", "白色": "white"}
            new_color = color_map[self.unified_color_var.get()]
            
            # 保存历史记录
            total_count = len(selected_actors) + len(selected_props)
            self.save_state_to_history(f"修改名称样式 ({total_count}个)")
            
            # 应用到演员
            for item in selected_actors:
                actor = item['item']
                if "name_char_styles_per_frame" not in actor:
                    actor["name_char_styles_per_frame"] = []
                while len(actor["name_char_styles_per_frame"]) < self.total_frames:
                    actor["name_char_styles_per_frame"].append([])
                
                for frame in range(self.current_frame, self.total_frames):
                    name = actor["name"]
                    if not name:
                        continue
                    frame_styles = actor["name_char_styles_per_frame"][frame]
                    default_color = actor.get("color", "blue")
                    while len(frame_styles) < len(name):
                        frame_styles.append({"font_size": actor.get("font_size", 10), "color": default_color})
                    if len(frame_styles) > len(name):
                        actor["name_char_styles_per_frame"][frame] = frame_styles[:len(name)]
                        frame_styles = actor["name_char_styles_per_frame"][frame]
                    for i in range(len(frame_styles)):
                        frame_styles[i]["font_size"] = new_font_size
                        frame_styles[i]["color"] = new_color
            
            # 应用到道具
            for item in selected_props:
                prop = item['item']
                if "name_char_styles_per_frame" not in prop:
                    prop["name_char_styles_per_frame"] = []
                while len(prop["name_char_styles_per_frame"]) < self.total_frames:
                    prop["name_char_styles_per_frame"].append([])
                
                for frame in range(self.current_frame, self.total_frames):
                    name = prop["name"]
                    if not name:
                        continue
                    frame_styles = prop["name_char_styles_per_frame"][frame]
                    default_color = prop.get("color", "red")
                    while len(frame_styles) < len(name):
                        frame_styles.append({"font_size": prop.get("font_size", 10), "color": default_color})
                    if len(frame_styles) > len(name):
                        prop["name_char_styles_per_frame"][frame] = frame_styles[:len(name)]
                        frame_styles = prop["name_char_styles_per_frame"][frame]
                    for i in range(len(frame_styles)):
                        frame_styles[i]["font_size"] = new_font_size
                        frame_styles[i]["color"] = new_color
            
            self.update_stage_preview()
            self.log(f"✓ 已更新 {total_count} 个对象的名称样式", 'success')
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))
    
    def apply_prop_name(self):
        """应用道具新名称"""
        try:
            # 检查是否有选中的道具
            selected_props = [item for item in self.selected_items if item['type'] == 'prop']
            
            if not selected_props:
                messagebox.showwarning("警告", "请先选中一个道具")
                return
            
            if len(selected_props) > 1:
                messagebox.showwarning("警告", "只能修改一个道具的名称")
                return
            
            # 获取新名称
            new_name = self.prop_name_entry.get().strip()
            if not new_name:
                raise ValueError("道具名称不能为空")
            
            # 获取选中的道具
            selected_item = selected_props[0]
            prop = selected_item['item']
            prop_index = selected_item['index']
            old_name = prop['name']
            
            # 更新道具名称
            prop['name'] = new_name
            
            # 保存历史记录
            self.save_state_to_history(f"修改道具名称: {old_name} → {new_name}")
            
            # 更新关键帧列表显示（道具在演员之后）
            list_index = len(self.actors) + prop_index
            self.keyframe_listbox.delete(list_index)
            self.keyframe_listbox.insert(list_index, f"道具: {new_name}")
            self.keyframe_listbox.selection_set(list_index)
            
            # 更新当前编辑标签
            self.current_item_label.config(text=f"当前编辑: 道具 {new_name}")
            
            # 更新显示
            self.update_stage_preview()
            
            # 记录日志
            self.log(f"✓ 道具名称已更新: {old_name} → {new_name}", 'success')
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))
    
    def apply_unified_fill(self):
        """统一的填充应用（根据选中的对象类型应用填充设置）"""
        selected_actors = [item for item in self.selected_items if item['type'] == 'actor']
        selected_props = [item for item in self.selected_items if item['type'] == 'prop']
        
        if not selected_actors and not selected_props:
            messagebox.showwarning("警告", "请先选中演员或道具")
            return
        
        try:
            # 获取填充设置
            fill_enabled = self.fill_enabled_var.get()
            fill_alpha = float(self.fill_alpha_entry.get())
            
            # 验证透明度范围
            if fill_alpha < 0.0 or fill_alpha > 1.0:
                raise ValueError("填充透明度必须在0.0到1.0之间")
            
            # 保存历史记录
            total_count = len(selected_actors) + len(selected_props)
            self.save_state_to_history(f"修改填充设置 ({total_count}个)")
            
            # 应用到演员
            for item in selected_actors:
                actor = item['item']
                actor["fill_enabled"] = fill_enabled
                actor["fill_alpha"] = fill_alpha
            
            # 应用到道具
            for item in selected_props:
                prop = item['item']
                prop["fill_enabled"] = fill_enabled
                prop["fill_alpha"] = fill_alpha
            
            self.update_stage_preview()
            self.log(f"✓ 已更新 {total_count} 个对象的填充设置 (启用:{fill_enabled}, 透明度:{fill_alpha:.2f})", 'success')
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))
    
    def toggle_style_detail_panel(self):
        """切换详细样式编辑面板的显示状态"""
        if self.style_detail_expanded.get():
            # 收起面板
            self.style_detail_panel.pack_forget()
            self.style_detail_toggle_btn.config(text="▶ 展开样式编辑")
            self.style_detail_expanded.set(False)
        else:
            # 展开面板
            self.style_detail_panel.pack(fill=tk.X, padx=2, pady=2)
            self.style_detail_toggle_btn.config(text="▼ 收起样式编辑")
            self.style_detail_expanded.set(True)
        
        # 内容变化后，更新滚动区域并检查滚动位置
        # 使用after确保布局更新完成后再检查
        self.root.after(10, lambda: self._check_canvas_scroll_position())
    
    def _check_canvas_scroll_position(self):
        """检查并修正Canvas滚动位置，防止出现空白"""
        try:
            if hasattr(self, 'control_canvas') and hasattr(self, 'control_canvas_window_id'):
                top, bottom = self.control_canvas.yview()
                # 如果滚动位置在顶部或接近顶部，确保窗口对象在正确位置
                if top <= 0.001:
                    self.control_canvas.yview_moveto(0)
                    self.control_canvas.coords(self.control_canvas_window_id, 0, 0)
                # 更新滚动区域
                bbox = self.control_canvas.bbox("all")
                if bbox:
                    self.control_canvas.configure(scrollregion=(0, 0, bbox[2], bbox[3]))
        except Exception as e:
            pass
    
    def apply_current_style(self):
        """应用当前样式（快捷方式）：边框颜色和文本字号"""
        selected_actors = [item for item in self.selected_items if item['type'] == 'actor']
        selected_props = [item for item in self.selected_items if item['type'] == 'prop']
        
        if not selected_actors and not selected_props:
            messagebox.showwarning("警告", "请先选中演员或道具")
            return
        
        try:
            # 获取快捷设置
            border_color = self.color_map.get(self.style_border_color_var.get(), "blue")
            text_size = float(self.style_text_size.get())
            
            if text_size <= 0:
                raise ValueError("文本字号必须大于0")
            
            # 保存历史记录
            total_count = len(selected_actors) + len(selected_props)
            self.save_state_to_history(f"应用样式 ({total_count}个)")
            
            # 应用到选中对象的当前帧
            current_frame = self.current_frame
            
            for item in selected_actors + selected_props:
                obj = item['item']
                
                # 确保styles_per_frame存在且长度正确
                if "styles_per_frame" not in obj or len(obj["styles_per_frame"]) != self.total_frames:
                    # 创建或修复styles_per_frame
                    default_style = {
                        "border_color": obj.get("color", "blue"),
                        "border_width": 2,
                        "border_style": "solid",
                        "border_alpha": 1.0,
                        "fill_enabled": obj.get("fill_enabled", False),
                        "fill_color": obj.get("color", "blue"),
                        "fill_alpha": obj.get("fill_alpha", 1.0),
                        "text_color": obj.get("color", "blue"),
                        "text_size": obj.get("font_size", 10),
                        "text_bold": False,
                        "text_italic": False,
                        "text_underline": False,
                        "text_alpha": 1.0,
                    }
                    obj["styles_per_frame"] = [default_style.copy() for _ in range(self.total_frames)]
                    obj["style_keyframes"] = []
                
                # 更新当前帧的样式
                obj["styles_per_frame"][current_frame]["border_color"] = border_color
                obj["styles_per_frame"][current_frame]["text_color"] = border_color  # 文本颜色与边框相同
                obj["styles_per_frame"][current_frame]["text_size"] = text_size
                
                # 添加样式关键帧（如果不存在）
                if current_frame not in obj.get("style_keyframes", []):
                    obj.setdefault("style_keyframes", []).append(current_frame)
                    obj["style_keyframes"].sort()
                
                # 更新向后兼容的属性
                obj["color"] = border_color
                obj["font_size"] = text_size
            
            # 应用样式到后续帧（直到下一个样式关键帧）
            self._propagate_styles_to_next_keyframe(selected_actors + selected_props, current_frame)
            
            self.update_stage_preview()
            self.log(f"✓ 已应用样式到 {total_count} 个对象（当前时间点）", 'success')
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))
    
    def apply_detailed_style(self):
        """应用详细样式设置"""
        selected_actors = [item for item in self.selected_items if item['type'] == 'actor']
        selected_props = [item for item in self.selected_items if item['type'] == 'prop']
        
        if not selected_actors and not selected_props:
            messagebox.showwarning("警告", "请先选中演员或道具")
            return
        
        try:
            # 获取详细样式设置
            border_color = self.color_map.get(self.style_border_color_var.get(), "blue")
            border_width = float(self.style_border_width.get())
            border_style_map = {"实线": "solid", "虚线": "dashed", "点线": "dotted", "点划线": "dashdot"}
            border_style = border_style_map.get(self.style_border_style_var.get(), "solid")
            border_alpha = float(self.style_border_alpha.get())
            
            fill_enabled = self.style_fill_enabled_var.get()
            fill_color = self.color_map.get(self.style_fill_color_var.get(), "blue")
            fill_alpha = float(self.style_fill_alpha.get())
            
            text_color = self.color_map.get(self.style_text_color_var.get(), "blue")
            text_size = float(self.style_text_size.get())
            text_bold = self.style_text_bold_var.get()
            text_italic = self.style_text_italic_var.get()
            text_underline = self.style_text_underline_var.get()
            text_alpha = float(self.style_text_alpha.get())
            
            # 验证数值范围
            if border_width <= 0:
                raise ValueError("边框线宽必须大于0")
            if not (0.0 <= border_alpha <= 1.0):
                raise ValueError("边框透明度必须在0.0到1.0之间")
            if not (0.0 <= fill_alpha <= 1.0):
                raise ValueError("填充透明度必须在0.0到1.0之间")
            if text_size <= 0:
                raise ValueError("文本字号必须大于0")
            if not (0.0 <= text_alpha <= 1.0):
                raise ValueError("文本透明度必须在0.0到1.0之间")
            
            # 保存历史记录
            total_count = len(selected_actors) + len(selected_props)
            self.save_state_to_history(f"应用详细样式 ({total_count}个)")
            
            # 应用到选中对象的当前帧
            current_frame = self.current_frame
            
            for item in selected_actors + selected_props:
                obj = item['item']
                
                # 确保styles_per_frame存在
                if "styles_per_frame" not in obj or len(obj["styles_per_frame"]) != self.total_frames:
                    default_style = {
                        "border_color": obj.get("color", "blue"),
                        "border_width": 2,
                        "border_style": "solid",
                        "border_alpha": 1.0,
                        "fill_enabled": obj.get("fill_enabled", False),
                        "fill_color": obj.get("color", "blue"),
                        "fill_alpha": obj.get("fill_alpha", 1.0),
                        "text_color": obj.get("color", "blue"),
                        "text_size": obj.get("font_size", 10),
                        "text_bold": False,
                        "text_italic": False,
                        "text_underline": False,
                        "text_alpha": 1.0,
                    }
                    obj["styles_per_frame"] = [default_style.copy() for _ in range(self.total_frames)]
                    obj["style_keyframes"] = []
                
                # 更新当前帧的完整样式
                obj["styles_per_frame"][current_frame].update({
                    "border_color": border_color,
                    "border_width": border_width,
                    "border_style": border_style,
                    "border_alpha": border_alpha,
                    "fill_enabled": fill_enabled,
                    "fill_color": fill_color,
                    "fill_alpha": fill_alpha,
                    "text_color": text_color,
                    "text_size": text_size,
                    "text_bold": text_bold,
                    "text_italic": text_italic,
                    "text_underline": text_underline,
                    "text_alpha": text_alpha,
                })
                
                # 添加样式关键帧
                if current_frame not in obj.get("style_keyframes", []):
                    obj.setdefault("style_keyframes", []).append(current_frame)
                    obj["style_keyframes"].sort()
                
                # 更新向后兼容的属性
                obj["color"] = border_color
                obj["font_size"] = text_size
                obj["fill_enabled"] = fill_enabled
                obj["fill_alpha"] = fill_alpha
            
            # 应用样式到后续帧
            self._propagate_styles_to_next_keyframe(selected_actors + selected_props, current_frame)
            
            self.update_stage_preview()
            self.log(f"✓ 已应用详细样式到 {total_count} 个对象", 'success')
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))
    
    def _propagate_styles_to_next_keyframe(self, selected_items, start_frame):
        """将样式传播到下一个关键帧之前的所有帧"""
        for item in selected_items:
            obj = item['item']
            
            if "styles_per_frame" not in obj or "style_keyframes" not in obj:
                continue
            
            # 找到下一个样式关键帧
            next_keyframe = None
            for kf in obj["style_keyframes"]:
                if kf > start_frame:
                    next_keyframe = kf
                    break
            
            # 确定结束帧
            end_frame = next_keyframe if next_keyframe is not None else self.total_frames
            
            # 复制当前帧的样式到后续帧
            current_style = obj["styles_per_frame"][start_frame].copy()
            for frame in range(start_frame + 1, end_frame):
                obj["styles_per_frame"][frame] = current_style.copy()
    
    def copy_style(self):
        """复制选中对象的当前样式"""
        selected_actors = [item for item in self.selected_items if item['type'] == 'actor']
        selected_props = [item for item in self.selected_items if item['type'] == 'prop']
        
        if not selected_actors and not selected_props:
            messagebox.showwarning("警告", "请先选中演员或道具")
            return
        
        # 复制第一个选中对象的当前帧样式
        obj = (selected_actors + selected_props)[0]['item']
        
        if "styles_per_frame" in obj and len(obj["styles_per_frame"]) > self.current_frame:
            self.style_clipboard = obj["styles_per_frame"][self.current_frame].copy()
            self.log("✓ 已复制样式", 'success')
        else:
            messagebox.showwarning("警告", "该对象没有可用的样式数据")
    
    def paste_style(self):
        """粘贴样式到选中对象"""
        if self.style_clipboard is None:
            messagebox.showwarning("警告", "请先复制样式")
            return
        
        selected_actors = [item for item in self.selected_items if item['type'] == 'actor']
        selected_props = [item for item in self.selected_items if item['type'] == 'prop']
        
        if not selected_actors and not selected_props:
            messagebox.showwarning("警告", "请先选中演员或道具")
            return
        
        try:
            # 保存历史记录
            total_count = len(selected_actors) + len(selected_props)
            self.save_state_to_history(f"粘贴样式 ({total_count}个)")
            
            current_frame = self.current_frame
            
            for item in selected_actors + selected_props:
                obj = item['item']
                
                # 确保styles_per_frame存在
                if "styles_per_frame" not in obj or len(obj["styles_per_frame"]) != self.total_frames:
                    default_style = self.style_clipboard.copy()
                    obj["styles_per_frame"] = [default_style.copy() for _ in range(self.total_frames)]
                    obj["style_keyframes"] = []
                
                # 粘贴样式到当前帧
                obj["styles_per_frame"][current_frame] = self.style_clipboard.copy()
                
                # 添加样式关键帧
                if current_frame not in obj.get("style_keyframes", []):
                    obj.setdefault("style_keyframes", []).append(current_frame)
                    obj["style_keyframes"].sort()
                
                # 更新向后兼容的属性
                obj["color"] = self.style_clipboard.get("border_color", "blue")
                obj["font_size"] = self.style_clipboard.get("text_size", 10)
                obj["fill_enabled"] = self.style_clipboard.get("fill_enabled", False)
                obj["fill_alpha"] = self.style_clipboard.get("fill_alpha", 1.0)
            
            # 应用样式到后续帧
            self._propagate_styles_to_next_keyframe(selected_actors + selected_props, current_frame)
            
            self.update_stage_preview()
            self.log(f"✓ 已粘贴样式到 {total_count} 个对象", 'success')
            
        except Exception as e:
            messagebox.showerror("错误", f"粘贴样式失败：{str(e)}")
    
    def reset_style_to_default(self):
        """重置选中对象的样式为默认值"""
        selected_actors = [item for item in self.selected_items if item['type'] == 'actor']
        selected_props = [item for item in self.selected_items if item['type'] == 'prop']
        
        if not selected_actors and not selected_props:
            messagebox.showwarning("警告", "请先选中演员或道具")
            return
        
        try:
            # 保存历史记录
            total_count = len(selected_actors) + len(selected_props)
            self.save_state_to_history(f"重置样式 ({total_count}个)")
            
            current_frame = self.current_frame
            
            for item in selected_actors + selected_props:
                obj = item['item']
                
                # 默认样式
                default_style = {
                    "border_color": obj.get("color", "blue"),
                    "border_width": 2,
                    "border_style": "solid",
                    "border_alpha": 1.0,
                    "fill_enabled": False,
                    "fill_color": obj.get("color", "blue"),
                    "fill_alpha": 1.0,
                    "text_color": obj.get("color", "blue"),
                    "text_size": obj.get("font_size", 10),
                    "text_bold": False,
                    "text_italic": False,
                    "text_underline": False,
                    "text_alpha": 1.0,
                }
                
                # 确保styles_per_frame存在
                if "styles_per_frame" not in obj or len(obj["styles_per_frame"]) != self.total_frames:
                    obj["styles_per_frame"] = [default_style.copy() for _ in range(self.total_frames)]
                    obj["style_keyframes"] = []
                
                # 重置当前帧样式
                obj["styles_per_frame"][current_frame] = default_style.copy()
                
                # 添加样式关键帧
                if current_frame not in obj.get("style_keyframes", []):
                    obj.setdefault("style_keyframes", []).append(current_frame)
                    obj["style_keyframes"].sort()
            
            # 应用样式到后续帧
            self._propagate_styles_to_next_keyframe(selected_actors + selected_props, current_frame)
            
            self.update_stage_preview()
            self.log(f"✓ 已重置 {total_count} 个对象的样式", 'success')
            
        except Exception as e:
            messagebox.showerror("错误", f"重置样式失败：{str(e)}")
    
    def delete_actor(self):
        """删除选中的演员（支持批量删除）"""
        # 优先使用多选列表中的演员
        actors_to_delete = [item for item in self.selected_items if item['type'] == 'actor']
        
        if actors_to_delete:
            # 批量删除模式
            actor_names = ', '.join([item['item']['name'] for item in actors_to_delete])
            
            # 确认删除
            if not messagebox.askyesno("确认", f"确定要删除 {len(actors_to_delete)} 个演员吗？\n{actor_names}"):
                return
            
            # 保存历史记录
            self.save_state_to_history(f"批量删除演员 ({len(actors_to_delete)}个)")
            
            # 删除演员
            actors_to_delete_objs = [item['item'] for item in actors_to_delete]
            self.actors = [actor for actor in self.actors if actor not in actors_to_delete_objs]
            
            # 清空选中列表
            self.selected_items.clear()
            
            # 重建列表显示
            self.keyframe_listbox.delete(0, tk.END)
            for actor in self.actors:
                self.keyframe_listbox.insert(tk.END, f"演员: {actor['name']}")
            for prop in self.props:
                self.keyframe_listbox.insert(tk.END, f"道具: {prop['name']}")
            
            # 清空关键帧表格
            for row in self.keyframe_tree.get_children():
                self.keyframe_tree.delete(row)
            
            # 更新舞台预览
            self.update_stage_preview()
            
            # 显示成功提示
            self.log(f"✓ 已删除 {len(actors_to_delete)} 个演员", 'success')
        else:
            # 单个删除模式（原有逻辑）
            selected = self.keyframe_listbox.curselection()
            if not selected:
                messagebox.showwarning("警告", "请先选择一个演员")
                return
                
            index = selected[0]
            if index >= len(self.actors):
                messagebox.showwarning("警告", "请选择一个演员")
                return
                
            # 确认删除
            if not messagebox.askyesno("确认", f"确定要删除演员 {self.actors[index]['name']} 吗？"):
                return
            
            # 保存历史记录
            self.save_state_to_history(f"删除演员 ({self.actors[index]['name']})")
                
            # 删除演员
            del self.actors[index]
            
            # 更新列表显示
            self.keyframe_listbox.delete(index)
            
            # 清空关键帧表格
            for row in self.keyframe_tree.get_children():
                self.keyframe_tree.delete(row)
            
            # 更新舞台预览
            self.update_stage_preview()
            
            # 显示成功提示
            self.log("✓ 演员已删除", 'success')
        
    def delete_prop(self):
        """删除选中的道具（支持批量删除）"""
        # 优先使用多选列表中的道具
        props_to_delete = [item for item in self.selected_items if item['type'] == 'prop']
        
        if props_to_delete:
            # 批量删除模式
            prop_names = ', '.join([item['item']['name'] for item in props_to_delete])
            
            # 确认删除
            if not messagebox.askyesno("确认", f"确定要删除 {len(props_to_delete)} 个道具吗？\n{prop_names}"):
                return
            
            # 保存历史记录
            self.save_state_to_history(f"批量删除道具 ({len(props_to_delete)}个)")
            
            # 删除道具
            props_to_delete_objs = [item['item'] for item in props_to_delete]
            self.props = [prop for prop in self.props if prop not in props_to_delete_objs]
            
            # 清空选中列表
            self.selected_items.clear()
            
            # 重建列表显示
            self.keyframe_listbox.delete(0, tk.END)
            for actor in self.actors:
                self.keyframe_listbox.insert(tk.END, f"演员: {actor['name']}")
            for prop in self.props:
                self.keyframe_listbox.insert(tk.END, f"道具: {prop['name']}")
            
            # 清空关键帧表格
            for row in self.keyframe_tree.get_children():
                self.keyframe_tree.delete(row)
            
            # 更新舞台预览
            self.update_stage_preview()
            
            # 显示成功提示
            self.log(f"✓ 已删除 {len(props_to_delete)} 个道具", 'success')
        else:
            # 单个删除模式（原有逻辑）
            selected = self.keyframe_listbox.curselection()
            if not selected:
                messagebox.showwarning("警告", "请先选择一个道具")
                return
                
            index = selected[0]
            if index < len(self.actors):
                messagebox.showwarning("警告", "请选择一个道具")
                return
                
            prop_index = index - len(self.actors)
            if prop_index >= len(self.props):
                messagebox.showwarning("警告", "请选择一个道具")
                return
                
            # 确认删除
            if not messagebox.askyesno("确认", f"确定要删除道具 {self.props[prop_index]['name']} 吗？"):
                return
            
            # 保存历史记录
            self.save_state_to_history(f"删除道具 ({self.props[prop_index]['name']})")
                
            # 删除道具
            del self.props[prop_index]
            
            # 更新列表显示
            self.keyframe_listbox.delete(index)
            
            # 清空关键帧表格
            for row in self.keyframe_tree.get_children():
                self.keyframe_tree.delete(row)
                
            # 更新舞台预览
            self.update_stage_preview()
            
            # 显示成功提示
            self.log("✓ 道具已删除", 'success')
    
    def switch_frame(self):
        """切换到指定时间"""
        try:
            seconds = float(self.frame_switch_entry.get())
            if seconds < 0 or seconds > self.total_seconds:  # 修改为 > 而不是 >=
                raise ValueError(f"时间必须在0到{self.total_seconds}秒之间")
            
            # 转换为帧数
            frame = int(seconds * self.fps)
            
            # 更新当前帧和时间
            self.current_frame = frame
            self.current_second = seconds
            self.time_scale.set(seconds)
            
            # 更新舞台预览
            self.update_stage_preview()
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))

    def on_speed_change(self, event):
        """处理播放速度变化事件"""
        try:
            # 从选择的值中提取速度数值（去掉'x'后缀）
            speed_str = self.speed_var.get().rstrip('x')
            new_speed = float(speed_str)
            if new_speed <= 0:
                raise ValueError("播放速度必须大于0")
            
            self.playback_speed = new_speed
            
            # 如果正在播放，重置时间记录
            if self.animation_loop.running:
                self.last_frame_time = self.root.tk.call('clock', 'milliseconds')
                self.fps_start_time = self.last_frame_time
                self.frame_count = 0
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))
            # 恢复原来的值
            self.speed_var.set(f"{self.playback_speed:.2f}x")

    def export_animation(self):
        """导出动画为GIF文件"""
        # 检查动画是否正在播放
        if hasattr(self, 'animation_loop') and self.animation_loop.running:
            messagebox.showwarning("警告", "请先停止动画播放再进行导出")
            return
        
        # 初始化进度窗口变量（在try块之前）
        progress_window = None
            
        try:
            # 获取导出帧率
            export_fps = int(self.export_fps_entry.get())
            if export_fps <= 0:
                raise ValueError("导出帧率必须大于0")
            
            # 创建导出目录
            export_dir = "exports"
            if not os.path.exists(export_dir):
                os.makedirs(export_dir)
            
            # 让用户选择保存位置
            export_path = filedialog.asksaveasfilename(
                defaultextension=".gif",
                initialdir=export_dir,
                initialfile="stage_animation.gif",
                filetypes=[("GIF files", "*.gif"), ("All files", "*.*")]
            )
            
            if not export_path:  # 用户取消选择
                return
            
            # 创建进度条窗口
            progress_window = tk.Toplevel(self.root)
            progress_window.title("GIF导出进度")
            progress_window.geometry("400x180")
            progress_window.resizable(False, False)
            
            # 设置窗口在主窗口前面
            progress_window.transient(self.root)
            progress_window.grab_set()
            
            # 添加进度标签
            progress_label = ttk.Label(progress_window, text="正在准备GIF导出...", font=('Arial', 10))
            progress_label.pack(pady=15)
            
            # 添加进度条
            progress_bar = ttk.Progressbar(progress_window, length=350, mode='determinate')
            progress_bar.pack(pady=10)
            
            # 添加状态标签
            status_label = ttk.Label(progress_window, text="初始化中...", font=('Arial', 9))
            status_label.pack(pady=5)
            
            # 添加帧计数标签
            frame_label = ttk.Label(progress_window, text="", font=('Arial', 8))
            frame_label.pack(pady=5)
            
            # 添加取消按钮
            cancel_button = ttk.Button(progress_window, text="取消", 
                                     command=lambda: setattr(self, '_cancel_export', True))
            cancel_button.pack(pady=10)
            
            # 初始化状态
            self._cancel_export = False
            start_time = time.time()
            
            # 更新窗口
            progress_window.update()
            
            # 计算需要导出的总帧数
            total_export_frames = int(self.total_seconds * export_fps)
            
            # 确保有帧数可以导出
            if total_export_frames <= 0:
                progress_window.destroy()
                raise ValueError("没有可导出的帧数")
            
            # 显示项目信息
            progress_label.config(text=f"准备导出 {total_export_frames} 帧GIF动画")
            frame_label.config(text=f"帧率: {export_fps} FPS | 时长: {self.total_seconds:.1f}秒")
            progress_window.update()
            
            # 创建临时目录存储帧
            temp_dir = tempfile.mkdtemp()
            
            # 在主线程中预先获取 tkinter 变量的值（避免线程安全问题）
            grid_enabled_value = self.grid_enabled.get()
            
            print(f"[GIF导出] 总帧数={total_export_frames}, 帧率={export_fps}, 辅助线={'开启' if grid_enabled_value else '关闭'}")
            
            try:
                # 单线程顺序渲染（避免 tkinter 线程安全问题）
                frame_files = []
                
                for frame in range(total_export_frames):
                    # 检查是否取消
                    if hasattr(self, '_cancel_export') and self._cancel_export:
                        raise Exception("用户取消导出")
                    
                    frame_path = os.path.join(temp_dir, f"frame_{frame:04d}.png")
                    
                    # 创建图形对象
                    export_fig = Figure(figsize=(10, 8), dpi=100)
                    export_ax = export_fig.add_subplot(111)
                    export_fig.patch.set_facecolor('white')
                    export_ax.set_facecolor('white')
                    
                    # 渲染帧内容，传入is_export=True
                    self.render_frame(export_ax, frame, export_fps, is_export=True)
                    
                    # 保存帧
                    export_fig.savefig(frame_path, 
                                      facecolor='white',
                                      edgecolor='none',
                                      dpi=100,
                                      pad_inches=0)
                    plt.close(export_fig)
                    frame_files.append((frame, frame_path))
                    
                    # 更新进度
                    completed_frames = frame + 1
                    progress = (completed_frames / total_export_frames) * 100
                    progress_bar['value'] = progress
                    
                    # 计算预计剩余时间
                    elapsed_time = time.time() - start_time
                    if completed_frames > 0:
                        avg_time_per_frame = elapsed_time / completed_frames
                        remaining_frames = total_export_frames - completed_frames
                        estimated_remaining = avg_time_per_frame * remaining_frames
                        
                        status_label.config(text=f"正在渲染帧 {completed_frames}/{total_export_frames}")
                        frame_label.config(text=f"已用时: {int(elapsed_time)}秒 | 预计剩余: {int(estimated_remaining)}秒")
                    
                    # 每10帧更新一次UI（减少UI更新频率，提升性能）
                    if completed_frames % 10 == 0 or completed_frames == total_export_frames:
                        progress_window.update()
                
                # 按帧序号排序
                frame_files.sort(key=lambda x: x[0])
                frame_paths = [path for _, path in frame_files]
                
                # 更新状态
                status_label.config(text="正在合成GIF...")
                frame_label.config(text="将所有帧合成为GIF文件")
                progress_window.update()
                
                # 使用PIL将所有帧合成为GIF
                frames = []
                for frame_path in frame_paths:
                    img = Image.open(frame_path)
                    frames.append(img)
                
                # 计算每帧持续时间（毫秒）
                duration = int(1000 / export_fps)
                
                # 保存GIF
                frames[0].save(
                    export_path,
                    save_all=True,
                    append_images=frames[1:],
                    duration=duration,
                    loop=0,
                    optimize=False  # 不优化，保证速度
                )
                
                # 关闭所有PIL图像
                for frame in frames:
                    frame.close()
                
                # 显示成功消息
                elapsed_time = time.time() - start_time
                status_label.config(text="导出完成！")
                frame_label.config(text=f"成功导出 {total_export_frames} 帧 | 总用时: {int(elapsed_time)}秒")
                progress_bar['value'] = 100
                cancel_button.config(text="关闭")
                progress_window.update()
                
                print(f"GIF导出完成: {export_path}")
                
                # 等待用户点击关闭或自动关闭
                progress_window.after(2000, progress_window.destroy)  # 2秒后自动关闭
                
                # 显示成功消息
                self.log(f"✓ GIF动画导出成功: {os.path.basename(export_path)}", 'success')
                
            finally:
                # 清理临时文件
                shutil.rmtree(temp_dir)
        
        except ValueError as e:
            if progress_window is not None:
                progress_window.destroy()
            messagebox.showerror("错误", str(e))
        except Exception as e:
            if progress_window is not None:
                progress_window.destroy()
            messagebox.showerror("错误", f"导出失败: {str(e)}")
            print(f"导出错误详情: {str(e)}")  # 添加详细错误信息打印
        finally:
            # 清理取消标志
            if hasattr(self, '_cancel_export'):
                delattr(self, '_cancel_export')

    def save_project(self):
        """保存当前项目"""
        try:
            # 让用户选择保存位置
            file_path = filedialog.asksaveasfilename(
                defaultextension=".json",
                filetypes=[("JSON files", "*.json"), ("All files", "*.*")],
                title="保存项目"
            )
            
            if not file_path:  # 用户取消选择
                return
            
            # 准备保存的数据
            project_data = {
                "stage_width": self.stage_width,
                "stage_height": self.stage_height,
                "total_frames": self.total_frames,
                "actors": self.actors,
                "props": self.props,
                "text_box": self.text_box,
                "textboxes": self.textboxes  # 新版文本框系统
            }
            
            # 保存到文件
            with open(file_path, 'w', encoding='utf-8') as f:
                json.dump(project_data, f, ensure_ascii=False, indent=2)
            
            # 显示成功消息
            self.log(f"✓ 项目已保存: {os.path.basename(file_path)}", 'success')
            
        except Exception as e:
            messagebox.showerror("错误", f"保存失败: {str(e)}")

    def load_project(self):
        """导入项目"""
        try:
            # 让用户选择文件
            file_path = filedialog.askopenfilename(
                filetypes=[("JSON files", "*.json"), ("All files", "*.*")],
                title="导入项目"
            )
            
            if not file_path:  # 用户取消选择
                return
            
            # 停止任何正在进行的动画
            if hasattr(self, 'animation_loop') and self.animation_loop.running:
                self.animation_loop.stop()
            
            # 读取文件
            with open(file_path, 'r', encoding='utf-8') as f:
                project_data = json.load(f)
            
            # 兼容性检查和数据修复
            print(f"正在导入项目文件: {file_path}")
            print(f"项目数据键: {list(project_data.keys())}")
            
            # 更新舞台尺寸
            self.stage_width = project_data.get("stage_width", 20)  # 默认值
            self.stage_height = project_data.get("stage_height", 15)  # 默认值
            self.width_entry.delete(0, tk.END)
            self.width_entry.insert(0, str(self.stage_width))
            self.height_entry.delete(0, tk.END)
            self.height_entry.insert(0, str(self.stage_height))
            
            # 更新总帧数
            self.total_frames = project_data.get("total_frames", 600)  # 默认值
            self.total_seconds = self.total_frames / self.fps
            
            # 更新演员和道具，确保兼容性
            self.actors = project_data.get("actors", [])
            self.props = project_data.get("props", [])
            
            # 为演员和道具添加缺失的字段
            for actor in self.actors:
                # 确保所有必需字段存在
                if "color" not in actor:
                    actor["color"] = "blue"
                if "font_size" not in actor:
                    actor["font_size"] = 10
                if "keyframes" not in actor:
                    actor["keyframes"] = [0]
                else:
                    # 确保关键帧是整数（修复字符串关键帧问题）
                    actor["keyframes"] = [int(f) for f in actor["keyframes"]]
                if "positions" not in actor or len(actor["positions"]) != self.total_frames:
                    # 重建位置数组
                    default_pos = (0, 5)
                    actor["positions"] = [default_pos for _ in range(self.total_frames)]
                # 添加旋转数据兼容性
                if "rotations" not in actor:
                    actor["rotations"] = [0.0 for _ in range(self.total_frames)]
                elif len(actor["rotations"]) != self.total_frames:
                    # 调整旋转数组长度
                    old_rotations = actor["rotations"]
                    actor["rotations"] = [0.0 for _ in range(self.total_frames)]
                    for i in range(min(len(old_rotations), self.total_frames)):
                        actor["rotations"][i] = old_rotations[i]
                if "rotation_keyframes" not in actor:
                    actor["rotation_keyframes"] = []
                else:
                    # 确保旋转关键帧是整数
                    actor["rotation_keyframes"] = [int(f) for f in actor["rotation_keyframes"]]
                    
            for prop in self.props:
                # 确保所有必需字段存在
                if "color" not in prop:
                    prop["color"] = "red"
                if "font_size" not in prop:
                    prop["font_size"] = 10
                if "keyframes" not in prop:
                    prop["keyframes"] = [0]
                else:
                    # 确保关键帧是整数（修复字符串关键帧问题）
                    prop["keyframes"] = [int(f) for f in prop["keyframes"]]
                if "positions" not in prop or len(prop["positions"]) != self.total_frames:
                    # 重建位置数组
                    default_pos = (0, 8)
                    prop["positions"] = [default_pos for _ in range(self.total_frames)]
                # 添加旋转数据兼容性
                if "rotations" not in prop:
                    prop["rotations"] = [0.0 for _ in range(self.total_frames)]
                elif len(prop["rotations"]) != self.total_frames:
                    # 调整旋转数组长度
                    old_rotations = prop["rotations"]
                    prop["rotations"] = [0.0 for _ in range(self.total_frames)]
                    for i in range(min(len(old_rotations), self.total_frames)):
                        prop["rotations"][i] = old_rotations[i]
                if "rotation_keyframes" not in prop:
                    prop["rotation_keyframes"] = []
                else:
                    # 确保旋转关键帧是整数
                    prop["rotation_keyframes"] = [int(f) for f in prop["rotation_keyframes"]]
            
            # 更新文本框
            self.text_box = project_data.get("text_box", {
                "contents": ["" for _ in range(self.total_frames)],
                "font_size": 12,
                "position": (0, self.stage_height + 1.5),
                "durations": {}
            })
            
            # 确保文本框字段完整
            if "contents" not in self.text_box:
                self.text_box["contents"] = ["" for _ in range(self.total_frames)]
            elif len(self.text_box["contents"]) != self.total_frames:
                # 调整文本内容数组长度
                old_contents = self.text_box["contents"]
                self.text_box["contents"] = ["" for _ in range(self.total_frames)]
                for i in range(min(len(old_contents), self.total_frames)):
                    self.text_box["contents"][i] = old_contents[i]
                    
            if "font_size" not in self.text_box:
                self.text_box["font_size"] = 12
            if "position" not in self.text_box:
                self.text_box["position"] = (0, self.stage_height + 1.5)
            if "durations" not in self.text_box:
                self.text_box["durations"] = {}
            else:
                # 确保durations字典的键是整数（修复字符串键问题）
                old_durations = self.text_box["durations"]
                self.text_box["durations"] = {}
                for start_frame, duration_frames in old_durations.items():
                    # 将字符串键转换为整数键
                    int_start_frame = int(start_frame)
                    int_duration_frames = int(duration_frames) if isinstance(duration_frames, str) else duration_frames
                    self.text_box["durations"][int_start_frame] = int_duration_frames
            
            # 更新新版文本框系统
            self.textboxes = project_data.get("textboxes", [])
            
            # 确保文本框字段完整性
            for textbox in self.textboxes:
                # 位置系统
                if "positions" not in textbox or len(textbox["positions"]) != self.total_frames:
                    default_pos = (0, self.stage_height + self.stage_height / 16)
                    textbox["positions"] = [default_pos for _ in range(self.total_frames)]
                if "keyframes" not in textbox:
                    textbox["keyframes"] = [0]
                else:
                    textbox["keyframes"] = [int(f) for f in textbox["keyframes"]]
                
                # 持续时间系统
                if "start_frame" not in textbox:
                    textbox["start_frame"] = 0
                if "duration_frames" not in textbox:
                    textbox["duration_frames"] = self.total_frames
                
                # 确保默认样式存在
                if "default_font_size" not in textbox:
                    textbox["default_font_size"] = 12
                if "default_color" not in textbox:
                    textbox["default_color"] = "black"
                
                # 每帧内容和样式系统（新版）
                if "contents" not in textbox:
                    # 从旧版格式转换
                    old_content = textbox.get("content", "")
                    textbox["contents"] = ["" for _ in range(self.total_frames)]
                    
                    # 如果有旧版content，在显示范围内填充
                    if old_content:
                        start_frame = textbox.get("start_frame", 0)
                        duration_frames = textbox.get("duration_frames", self.total_frames)
                        end_frame = start_frame + duration_frames
                        for frame in range(start_frame, min(end_frame, self.total_frames)):
                            textbox["contents"][frame] = old_content
                elif len(textbox["contents"]) != self.total_frames:
                    # 调整数组大小，保留现有内容
                    old_contents = textbox["contents"]
                    new_contents = ["" for _ in range(self.total_frames)]
                    for i in range(min(len(old_contents), self.total_frames)):
                        new_contents[i] = old_contents[i]
                    textbox["contents"] = new_contents
                    print(f"  文本框 {textbox['name']}: 调整contents数组 {len(old_contents)} → {self.total_frames} (已保留内容)")
                
                if "char_styles_per_frame" not in textbox:
                    textbox["char_styles_per_frame"] = [[] for _ in range(self.total_frames)]
                    
                    # 从旧版char_styles转换或初始化
                    if "char_styles" in textbox:
                        old_char_styles = textbox["char_styles"]
                        start_frame = textbox.get("start_frame", 0)
                        duration_frames = textbox.get("duration_frames", self.total_frames)
                        end_frame = start_frame + duration_frames
                        for frame in range(start_frame, min(end_frame, self.total_frames)):
                            if textbox["contents"][frame]:
                                textbox["char_styles_per_frame"][frame] = old_char_styles.copy()
                    else:
                        # 根据每帧的内容初始化样式
                        default_font_size = textbox.get("default_font_size", 12)
                        default_color = textbox.get("default_color", "black")
                        for frame in range(self.total_frames):
                            content = textbox["contents"][frame]
                            if content:
                                frame_styles = []
                                for _ in content:
                                    frame_styles.append({
                                        "font_size": default_font_size,
                                        "color": default_color
                                    })
                                textbox["char_styles_per_frame"][frame] = frame_styles
                elif len(textbox["char_styles_per_frame"]) != self.total_frames:
                    # 调整数组大小，保留现有样式
                    old_styles = textbox["char_styles_per_frame"]
                    new_styles = [[] for _ in range(self.total_frames)]
                    for i in range(min(len(old_styles), self.total_frames)):
                        new_styles[i] = old_styles[i]
                    textbox["char_styles_per_frame"] = new_styles
                    print(f"  文本框 {textbox['name']}: 调整char_styles数组 {len(old_styles)} → {self.total_frames} (已保留样式)")
            
            # 清空并更新关键帧列表
            self.keyframe_listbox.delete(0, tk.END)
            for actor in self.actors:
                self.keyframe_listbox.insert(tk.END, f"演员: {actor['name']}")
            for prop in self.props:
                self.keyframe_listbox.insert(tk.END, f"道具: {prop['name']}")
            for textbox in self.textboxes:
                self.keyframe_listbox.insert(tk.END, f"文本框: {textbox['name']}")
            
            # 更新时间轴
            self.time_scale.config(to=self.total_seconds)
            
            # 重置所有状态变量
            self.current_frame = 0
            self.current_second = 0
            self.is_playing = False
            self.fixed_view_range = None
            
            # 清理临时状态
            self.temp_position_overrides.clear()
            self.temp_keyframes.clear()
            
            # 重置拖动状态
            self.dragging = False
            self.drag_item = None
            self.drag_type = None
            self.drag_index = None
            self.drag_start_pos = None
            self.drag_end_pos = None
            
            # 重置时间轴滑块标志
            self.is_time_scale_updating = False
            
            # 更新时间轴滑块位置
            self.time_scale.set(0)
            
            # 更新总秒数显示
            self.seconds_entry.delete(0, tk.END)
            self.seconds_entry.insert(0, str(self.total_seconds))
            
            # 更新显示
            self.update_stage_preview()
            
            # 强制更新画布
            self.canvas.draw()
            
            print(f"项目导入成功: 演员{len(self.actors)}个, 道具{len(self.props)}个, 总时长{self.total_seconds}秒")
            
            # 显示成功消息
            self.log(f"✓ 项目已导入: 演员{len(self.actors)}个, 道具{len(self.props)}个, 总时长{self.total_seconds}秒", 'success')
            
        except Exception as e:
            error_msg = f"导入失败: {str(e)}"
            print(f"导入错误详情: {error_msg}")
            import traceback
            traceback.print_exc()
            messagebox.showerror("错误", error_msg)

    def update_stage_size(self):
        """更新舞台尺寸"""
        try:
            new_width = float(self.width_entry.get())
            new_height = float(self.height_entry.get())
            
            if new_width <= 0 or new_height <= 0:
                raise ValueError("舞台尺寸必须大于0")
                
            self.stage_width = new_width
            self.stage_height = new_height
            
            # 更新舞台预览
            self.update_stage_preview()
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))
            # 恢复原来的值
            self.width_entry.delete(0, tk.END)
            self.width_entry.insert(0, str(self.stage_width))
            self.height_entry.delete(0, tk.END)
            self.height_entry.insert(0, str(self.stage_height))

    def update_timeline_settings(self):
        """更新时间轴设置"""
        try:
            # 更新总秒数
            new_seconds = float(self.seconds_entry.get())
            if new_seconds <= 0:
                raise ValueError("总秒数必须大于0")
            new_frames = int(new_seconds * self.fps)
            old_frames = self.total_frames
            self.total_seconds = new_seconds
            self.total_frames = new_frames

            # 更新所有演员的位置数组
            for actor in self.actors:
                old_positions = actor["positions"]
                actor["positions"] = [(0, 0) for _ in range(new_frames)]
                for i in range(min(old_frames, new_frames)):
                    actor["positions"][i] = old_positions[i]
                actor["keyframes"] = [frame for frame in actor["keyframes"] if frame < new_frames]
                # 更新中间帧插值
                if len(actor["keyframes"]) >= 2:
                    self.update_intermediate_frames(actor)

            # 更新所有道具的位置数组
            for prop in self.props:
                old_positions = prop["positions"]
                prop["positions"] = [(0, 0) for _ in range(new_frames)]
                for i in range(min(old_frames, new_frames)):
                    prop["positions"][i] = old_positions[i]
                prop["keyframes"] = [frame for frame in prop["keyframes"] if frame < new_frames]
                # 更新中间帧插值
                if len(prop["keyframes"]) >= 2:
                    self.update_intermediate_frames(prop)

            # 更新旧版文本框内容数组
            old_contents = self.text_box["contents"]
            self.text_box["contents"] = ["" for _ in range(new_frames)]
            for i in range(min(old_frames, new_frames)):
                self.text_box["contents"][i] = old_contents[i]
            
            # 更新新版文本框系统
            for textbox in self.textboxes:
                # 更新位置数组
                if "positions" in textbox:
                    old_positions = textbox["positions"]
                    textbox["positions"] = [textbox["positions"][0] if textbox["positions"] else (0, 0) for _ in range(new_frames)]
                    for i in range(min(len(old_positions), new_frames)):
                        textbox["positions"][i] = old_positions[i]
                
                # 更新内容数组（保留现有内容）
                if "contents" in textbox:
                    old_contents = textbox["contents"]
                    textbox["contents"] = ["" for _ in range(new_frames)]
                    for i in range(min(len(old_contents), new_frames)):
                        textbox["contents"][i] = old_contents[i]
                
                # 更新样式数组（保留现有样式）
                if "char_styles_per_frame" in textbox:
                    old_styles = textbox["char_styles_per_frame"]
                    textbox["char_styles_per_frame"] = [[] for _ in range(new_frames)]
                    for i in range(min(len(old_styles), new_frames)):
                        textbox["char_styles_per_frame"][i] = old_styles[i]
                
                # 清理超出范围的关键帧
                if "keyframes" in textbox:
                    textbox["keyframes"] = [frame for frame in textbox["keyframes"] if frame < new_frames]

            # 更新时间轴滑块
            self.time_scale.config(to=new_seconds)
            
            # 如果当前时间超出新的总秒数，重置到开始
            if self.current_second >= new_seconds:
                self.current_second = 0
                self.current_frame = 0
                self.time_scale.set(0)
                
            self.update_stage_preview()
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))
            self.seconds_entry.delete(0, tk.END)
            self.seconds_entry.insert(0, str(self.total_seconds))

    def play_animation(self):
        """开始播放动画"""
        print("开始播放动画")
        try:
            # 设置播放状态并保存当前视图范围
            self.is_playing = True
            self.capture_current_view_range()
            
            # 清除临时位置覆盖（开始播放时）
            self.temp_position_overrides.clear()
            
            # 确保所有中间帧都已更新
            for actor in self.actors:
                if actor["keyframes"]:
                    self.update_intermediate_frames(actor)
            for prop in self.props:
                if prop["keyframes"]:
                    self.update_intermediate_frames(prop)
                    
            # 处理音频播放
            if self.audio_file:
                # 确保音量设置正确（防止拖动后音量为0的问题）
                if hasattr(self, '_dragging_muted') and self._dragging_muted:
                    self._dragging_muted = False
                    print(f"重置拖动静音标志")
                
                print(f"🎵 准备播放音频: 位置={self.current_second:.2f}秒, 目标音量={self.audio_volume:.2f}")
                
                # 停止当前播放
                pygame.mixer.music.stop()
                
                # 设置音量（在play之前）
                pygame.mixer.music.set_volume(self.audio_volume)
                
                # 开始播放
                pygame.mixer.music.play(loops=0, start=self.current_second)
                
                # 使用after延迟检查状态，不阻塞主线程
                def check_playback():
                    vol = pygame.mixer.music.get_volume()
                    busy = pygame.mixer.music.get_busy()
                    print(f"✅ 音频状态检查: 音量={vol:.2f}, 播放中={busy}")
                    if not busy:
                        print(f"⚠️ 警告：音频未在播放状态！")
                    if vol < 0.01:
                        print(f"⚠️ 警告：音量为0，重新设置...")
                        pygame.mixer.music.set_volume(self.audio_volume)
                
                self.root.after(200, check_playback)
                    
            # 启动动画循环
            self.animation_loop.start()
            print("动画循环已启动，视图范围已固定")
            
            # 记录日志
            self.log(f"▶ 开始播放 (从 {self.current_second:.1f}秒)", 'info')
        except Exception as e:
            print(f"播放动画时出错: {str(e)}")
            traceback.print_exc()

    def pause_animation(self):
        """暂停动画"""
        print("暂停动画")
        try:
            # 停止播放状态，恢复动态视图
            self.is_playing = False
            self.fixed_view_range = None
            
            self.animation_loop.stop()
            
            # 重置拖动静音标志
            if hasattr(self, '_dragging_muted'):
                self._dragging_muted = False
            
            # 暂停音频播放
            if self.audio_file and pygame.mixer.music.get_busy():
                pygame.mixer.music.pause()
            print("动画已暂停，视图范围已恢复")
            
            # 记录日志
            self.log(f"⏸ 暂停播放 (在 {self.current_second:.1f}秒)", 'info')
        except Exception as e:
            print(f"暂停动画时出错: {str(e)}")
            traceback.print_exc()

    def stop_animation(self):
        """停止动画"""
        print("停止动画")
        try:
            # 停止播放状态，恢复动态视图
            self.is_playing = False
            self.fixed_view_range = None
            
            self.animation_loop.stop()
            
            # 重置拖动静音标志并恢复音量
            if hasattr(self, '_dragging_muted'):
                self._dragging_muted = False
            if self.audio_file:
                pygame.mixer.music.set_volume(self.audio_volume)
            
            # 停止音频播放
            if self.audio_file:
                pygame.mixer.music.stop()
            self.current_second = 0
            self.current_frame = 0
            self.time_scale.set(0)
            self.update_stage_preview()
            print("动画已停止")
            
            # 记录日志
            self.log("⏹ 停止播放 (已重置到起点)", 'info')
        except Exception as e:
            print(f"停止动画时出错: {str(e)}")
            traceback.print_exc()

    def on_play_click(self, event):
        """处理播放按钮点击事件"""
        print("播放按钮被点击")  # 调试信息
        self.play_animation()

    def on_pause_click(self, event):
        """处理暂停按钮点击事件"""
        print("暂停按钮被点击")  # 调试信息
        self.pause_animation()

    def on_stop_click(self, event):
        """处理停止按钮点击事件"""
        print("停止按钮被点击")  # 调试信息
        self.stop_animation()
    
    def toggle_play_pause(self, event):
        """处理空格键：切换播放和暂停状态"""
        # 检查焦点是否在输入框上，如果是则允许正常输入空格
        focused_widget = self.root.focus_get()
        if focused_widget and isinstance(focused_widget, (tk.Entry, ttk.Entry, tk.Text)):
            # 如果焦点在输入框或文本框上，不拦截空格键，让其正常处理
            return
        
        # 检查是否正在播放
        if self.is_playing:
            print("空格键被按下 - 暂停动画")
            self.pause_animation()
        else:
            print("空格键被按下 - 播放动画")
            self.play_animation()
        # 返回"break"以阻止事件继续传播（防止触发按钮点击）
        return "break"

    def on_time_scale_press(self, event):
        """处理时间轴滑块按下事件"""
        # 标记用户正在拖动时间轴
        self.is_user_dragging_timeline = True
        print("用户开始拖动时间轴")
    
    def on_time_scale_change(self, value):
        """处理时间轴滑块变化事件"""
        # 如果正在更新滑块值，则跳过
        if self.is_time_scale_updating:
            return
            
        try:
            self.is_time_scale_updating = True
            
            # 获取秒数 - 播放过程中不应用吸附，只有用户手动操作时才吸附
            seconds = float(value)
            
            # 确保秒数不超过总秒数
            seconds = min(seconds, self.total_seconds)
            frame = int(seconds * self.fps)
            # 确保帧数不超过总帧数，并确保不小于0
            frame = max(0, min(frame, self.total_frames - 1))
            # 额外检查：确保帧数在文本框内容数组范围内
            if len(self.text_box["contents"]) > 0:
                frame = min(frame, len(self.text_box["contents"]) - 1)
            
            self.current_frame = frame
            self.current_second = seconds
            
            # 清理不再需要的临时关键帧
            self.cleanup_temp_keyframes_on_time_change()
            
            # 清除临时位置覆盖（当时间点改变时）
            self.temp_position_overrides.clear()
            
            # 重置拖动状态
            self.dragging = False
            self.drag_item = None
            self.drag_type = None
            self.drag_index = None
            self.drag_start_pos = None
            self.drag_end_pos = None
            
            # 拖动时不同步音频，避免卡顿（只在释放时同步）
            # 如果正在播放，暂时静音但不停止
            if self.audio_file and hasattr(self, 'animation_loop') and self.animation_loop.running:
                if not hasattr(self, '_dragging_muted') or not self._dragging_muted:
                    # 保存当前实际音量，如果为0则使用self.audio_volume
                    current_vol = pygame.mixer.music.get_volume()
                    self._pre_drag_volume = current_vol if current_vol > 0.01 else self.audio_volume
                    pygame.mixer.music.set_volume(0.0)
                    self._dragging_muted = True
                    print(f"拖动时间轴，音频临时静音（保存音量: {self._pre_drag_volume:.2f}）")
            
            # 更新舞台预览
            self.update_stage_preview()
            
        finally:
            self.is_time_scale_updating = False

    def on_time_scale_release(self, event):
        """处理时间轴滑块释放事件"""
        # 取消用户拖动标记
        self.is_user_dragging_timeline = False
        print("用户释放时间轴")
        
        # 如果正在更新滑块值，则跳过
        if self.is_time_scale_updating:
            return
            
        try:
            self.is_time_scale_updating = True
            
            # 获取当前秒数并应用吸附逻辑（使用自定义吸附间隔）
            raw_seconds = float(self.time_scale.get())
            # 根据自定义间隔进行吸附
            seconds = round(raw_seconds / self.snap_interval) * self.snap_interval
            
            # 更新滑块到吸附后的位置
            self.time_scale.set(seconds)
            
            # 确保秒数不超过总秒数
            seconds = min(seconds, self.total_seconds)
            frame = int(seconds * self.fps)
            # 确保帧数不超过总帧数，并确保不小于0
            frame = max(0, min(frame, self.total_frames - 1))
            # 额外检查：确保帧数在文本框内容数组范围内
            if len(self.text_box["contents"]) > 0:
                frame = min(frame, len(self.text_box["contents"]) - 1)
            
            self.current_frame = frame
            self.current_second = seconds
            
            # 重置拖动状态
            self.dragging = False
            self.drag_item = None
            self.drag_type = None
            self.drag_index = None
            self.drag_start_pos = None
            self.drag_end_pos = None
            
            # 如果有音频文件，同步音频位置（只在正在播放时）
            if self.audio_file:
                # 检查动画是否正在播放
                is_playing = hasattr(self, 'animation_loop') and self.animation_loop.running
                
                # 恢复拖动前的音量
                if hasattr(self, '_dragging_muted') and self._dragging_muted:
                    target_volume = self._pre_drag_volume if hasattr(self, '_pre_drag_volume') else self.audio_volume
                    print(f"恢复拖动前音量: {target_volume:.2f} (来自_pre_drag_volume)")
                    self._dragging_muted = False
                else:
                    target_volume = self.audio_volume
                    print(f"使用默认音量: {target_volume:.2f}")
                
                # 确保音量设置正确（多次设置确保生效）
                pygame.mixer.music.set_volume(target_volume)
                pygame.mixer.music.set_volume(target_volume)
                pygame.mixer.music.set_volume(target_volume)
                print(f"时间轴滑块释放，音量设置为: {target_volume:.2f}")
                
                # 只有在播放状态下才重新同步音频
                if is_playing:
                    print(f"播放中，同步音频到 {self.current_second:.2f} 秒，音量={target_volume:.2f}")
                    try:
                        # 简单直接的同步方式（不使用淡入淡出和sleep）
                        pygame.mixer.music.stop()
                        
                        # 播放前再次确保音量正确
                        pygame.mixer.music.set_volume(target_volume)
                        pygame.mixer.music.set_volume(target_volume)
                        
                        pygame.mixer.music.play(loops=0, start=self.current_second)
                        
                        # 使用after延迟检查播放状态，确保音频真正开始播放
                        def verify_playback():
                            is_busy = pygame.mixer.music.get_busy()
                            vol = pygame.mixer.music.get_volume()
                            print(f"✅ 拖动后音频状态: 播放中={is_busy}, 音量={vol:.2f}")
                            
                            # 检查音量是否正确
                            if vol < 0.01:
                                print(f"⚠️ 警告：音量为0，强制恢复到 {target_volume:.2f}")
                                pygame.mixer.music.set_volume(target_volume)
                                pygame.mixer.music.set_volume(target_volume)  # 设置两次确保生效
                                
                            # 检查是否在播放
                            if not is_busy:
                                print(f"⚠️ 警告：拖动后音频未播放，尝试重新播放...")
                                pygame.mixer.music.set_volume(target_volume)
                                pygame.mixer.music.play(loops=0, start=self.current_second)
                        
                        self.root.after(100, verify_playback)
                        
                        # 更新动画循环的音频同步状态
                        if hasattr(self, 'animation_loop'):
                            self.animation_loop.audio_start_time = self.root.tk.call('clock', 'milliseconds')
                            self.animation_loop.audio_started = True
                            # 重置同步检查时间
                            if hasattr(self.animation_loop, 'last_sync_check'):
                                self.animation_loop.last_sync_check = self.animation_loop.audio_start_time
                    except Exception as e:
                        print(f"⚠️ 音频同步失败: {e}")
                        traceback.print_exc()
                else:
                    # 如果没有在播放，只停止音频（不重新播放）
                    print(f"未播放状态，停止音频")
                    pygame.mixer.music.stop()
            
            # 更新舞台预览
            self.update_stage_preview()
            
            # update_stage_preview 已经包含了 draw_idle()，不需要再次调用
            
        finally:
            self.is_time_scale_updating = False

    def export_animation_with_audio(self):
        """导出带音频的动画"""
        # 检查动画是否正在播放
        if hasattr(self, 'animation_loop') and self.animation_loop.running:
            messagebox.showwarning("警告", "请先停止动画播放再进行导出")
            return
            
        if not self.audio_file:
            messagebox.showwarning("警告", "请先导入音频文件")
            return
            
        try:
            # 获取导出帧率
            export_fps = int(self.export_fps_entry.get())
            if export_fps <= 0:
                raise ValueError("导出帧率必须大于0")
            
            # 创建临时目录
            temp_dir = tempfile.mkdtemp()
            
            try:
                # 创建导出目录
                export_dir = "exports"
                if not os.path.exists(export_dir):
                    os.makedirs(export_dir)
                
                # 让用户选择保存位置
                export_path = filedialog.asksaveasfilename(
                    defaultextension=".mp4",
                    initialdir=export_dir,
                    initialfile="stage_animation_with_audio.mp4",
                    filetypes=[("MP4 files", "*.mp4"), ("All files", "*.*")]
                )
                
                if not export_path:  # 用户取消选择
                    return
                
                # 创建进度条窗口
                progress_window = tk.Toplevel(self.root)
                progress_window.title("MP4带音频导出进度")
                progress_window.geometry("450x220")
                progress_window.resizable(False, False)
                progress_window.transient(self.root)
                progress_window.grab_set()
                
                # 添加UI元素
                main_label = ttk.Label(progress_window, text="正在导出带音频的MP4动画...", font=('Arial', 12, 'bold'))
                main_label.pack(pady=15)
                progress_bar = ttk.Progressbar(progress_window, length=400, mode='determinate')
                progress_bar.pack(pady=10)
                status_label = ttk.Label(progress_window, text="初始化中...", font=('Arial', 10))
                status_label.pack(pady=5)
                detail_label = ttk.Label(progress_window, text="", font=('Arial', 9))
                detail_label.pack(pady=5)
                time_label = ttk.Label(progress_window, text="", font=('Arial', 8))
                time_label.pack(pady=5)
                cancel_button = ttk.Button(progress_window, text="取消", 
                                         command=lambda: setattr(self, '_cancel_export', True))
                cancel_button.pack(pady=10)
                
                # 初始化状态
                self._cancel_export = False
                start_time = time.time()
                total_export_frames = int(self.total_seconds * export_fps)
                
                # 显示项目信息
                status_label.config(text=f"准备导出 {total_export_frames} 帧")
                detail_label.config(text=f"帧率: {export_fps} FPS | 时长: {self.total_seconds:.1f}秒 | 音频: {os.path.basename(self.audio_file)}")
                progress_window.update()
                
                # 在主线程中预先获取 tkinter 变量的值（避免线程安全问题）
                grid_enabled_value = self.grid_enabled.get()
                
                print(f"[MP4导出] 总帧数={total_export_frames}, 帧率={export_fps}, 辅助线={'开启' if grid_enabled_value else '关闭'}")
                
                try:
                    frame_files = []
                    completed_frames = 0
                    
                    # 单线程顺序渲染（避免 tkinter 线程安全问题）
                    for frame in range(total_export_frames):
                        # 检查是否取消
                        if hasattr(self, '_cancel_export') and self._cancel_export:
                            raise Exception("用户取消导出")
                        
                        frame_path = os.path.join(temp_dir, f"frame_{frame:04d}.png")
                        
                        # 创建图形对象
                        export_fig = Figure(figsize=(10, 8), dpi=100)
                        export_ax = export_fig.add_subplot(111)
                        export_fig.patch.set_facecolor('white')
                        export_ax.set_facecolor('white')
                        
                        # 渲染帧内容，传入is_export=True
                        self.render_frame(export_ax, frame, export_fps, is_export=True)
                        
                        # 保存帧
                        export_fig.savefig(frame_path, 
                                          facecolor='white',
                                          edgecolor='none',
                                          dpi=100,
                                          pad_inches=0)
                        plt.close(export_fig)
                        frame_files.append(frame_path)
                        
                        # 更新进度
                        completed_frames += 1
                        progress = (completed_frames / total_export_frames) * 100
                        progress_bar['value'] = progress
                        
                        # 计算预计剩余时间
                        elapsed_time = time.time() - start_time
                        if completed_frames > 0:
                            avg_time_per_frame = elapsed_time / completed_frames
                            remaining_frames = total_export_frames - completed_frames
                            estimated_remaining = avg_time_per_frame * remaining_frames
                            
                            status_label.config(text=f"正在渲染帧 {completed_frames}/{total_export_frames}")
                            time_label.config(text=f"已用时: {int(elapsed_time)}秒 | 预计剩余: {int(estimated_remaining)}秒")
                        
                        # 每10帧更新一次UI（减少UI更新频率，提升性能）
                        if completed_frames % 10 == 0 or completed_frames == total_export_frames:
                            progress_window.update()
                    
                    # 按帧序号排序
                    frame_files.sort()
                    
                    # 更新状态
                    status_label.config(text="正在创建视频...")
                    progress_window.update()
                    
                    # 创建视频剪辑
                    video_clip = ImageSequenceClip(frame_files, fps=export_fps)
                    audio_clip = AudioFileClip(self.audio_file)
                    
                    # 确保音视频时长匹配
                    if audio_clip.duration > video_clip.duration:
                        audio_clip = audio_clip.subclipped(0, video_clip.duration)  # type: ignore
                    else:
                        video_clip = video_clip.with_duration(audio_clip.duration)  # type: ignore
                    
                    final_clip = video_clip.with_audio(audio_clip)  # type: ignore
                    
                    # 更新状态
                    status_label.config(text="正在导出最终视频...")
                    progress_window.update()
                    
                    # 使用优化的编码参数
                    cpu_count_for_encoding = os.cpu_count() or 4  # 如果cpu_count返回None，使用默认值4
                    
                    # 确保ffmpeg可用（对于打包后的exe）
                    # moviepy会自动使用imageio_ffmpeg提供的ffmpeg
                    
                    final_clip.write_videofile(
                        export_path,
                        codec='libx264',
                        audio_codec='aac',
                        fps=export_fps,
                        preset='ultrafast',  # 使用最快的编码预设
                        threads=min(cpu_count_for_encoding, 4),  # 使用多线程编码
                        bitrate='2000k',
                        audio_bitrate='128k',
                        logger=None  # 禁用详细日志输出
                    )
                    
                    # 清理资源
                    final_clip.close()
                    video_clip.close()
                    audio_clip.close()
                    
                    # 显示成功消息
                    self.log(f"✓ 带音频MP4导出成功: {os.path.basename(export_path)}", 'success')
                    
                except Exception as e:
                    raise Exception(f"导出过程中出错: {str(e)}")
                    
                finally:
                    # 关闭进度窗口
                    progress_window.destroy()
                    
            finally:
                # 清理临时文件
                shutil.rmtree(temp_dir)
                
        except Exception as e:
            messagebox.showerror("错误", f"导出失败: {str(e)}")
            print(f"导出错误详情: {str(e)}")
            traceback.print_exc()

    def render_frame(self, ax, frame, export_fps, is_export=False):
        """渲染单个帧
        Args:
            ax: matplotlib轴对象
            frame: 当前帧号
            export_fps: 导出帧率
            is_export: 是否是导出模式（影响渲染样式）
        """
        # 计算当前时间点
        current_time = frame / export_fps
        current_frame = int(current_time * self.fps)
        current_frame = min(current_frame, self.total_frames - 1)
        
        # 设置显示范围 - 调整Y轴范围以显示观众区域
        invisible_width = self.stage_width / 8  # 左右备台区域宽度
        ax.set_xlim(-self.stage_width/2 - invisible_width, self.stage_width/2 + invisible_width)
        # 计算后方备台区域高度以调整视图范围
        backstage_height = self.stage_height / 8
        ax.set_ylim(-2, self.stage_height + backstage_height + 1)  # 包含后方备台区域
        
        # 设置固定的长宽比，确保舞台和对象不会变形
        ax.set_aspect('equal', adjustable='box')
        
        # 绘制舞台边界
        stage_rect = Rectangle((-self.stage_width/2, 0), self.stage_width, self.stage_height, 
                             fill=False, color='black', linewidth=2)
        ax.add_patch(stage_rect)
        
        # 绘制舞台中线（红色虚线）
        ax.plot([0, 0], [0, self.stage_height], 'r--', linewidth=0.8, alpha=0.5)
        
        # 绘制备台区域
        invisible_width = self.stage_width / 8  # 左右备台区域宽度为舞台宽度的1/8
        
        # 左侧备台区域
        left_invisible = Rectangle((-self.stage_width/2 - invisible_width, 0), 
                                 invisible_width, self.stage_height,
                                 fill=True, color='gray', alpha=0.3)
        ax.add_patch(left_invisible)
        ax.text(-self.stage_width/2 - invisible_width/2, self.stage_height/2, '左侧\n备台区域', 
                 rotation=90, ha='center', va='center', color='gray', alpha=0.7, fontsize=12)
        
        # 右侧备台区域
        right_invisible = Rectangle((self.stage_width/2, 0), 
                                  invisible_width, self.stage_height,
                                  fill=True, color='gray', alpha=0.3)
        ax.add_patch(right_invisible)
        ax.text(self.stage_width/2 + invisible_width/2, self.stage_height/2, '右侧\n备台区域', 
                 rotation=90, ha='center', va='center', color='gray', alpha=0.7, fontsize=12)
        
        # 后方备台区域 - 连接左右两侧
        backstage_height = self.stage_height / 8  # 后方备台区域高度为舞台高度的1/8
        upper_backstage = Rectangle((-self.stage_width/2 - invisible_width, self.stage_height), 
                                   self.stage_width + 2 * invisible_width, backstage_height,
                                   fill=True, color='gray', alpha=0.3)
        ax.add_patch(upper_backstage)
        ax.text(0, self.stage_height + backstage_height/2, '后方备台区域', 
                 ha='center', va='center', color='gray', alpha=0.7, fontsize=12)
        
        # 添加观众区域标识 - 调整位置和样式
        ax.text(0, -1, '观众区域', ha='center', va='center', 
                color='gray', alpha=0.7, fontsize=12,
                bbox=dict(facecolor='white', alpha=0.3, edgecolor='gray', pad=3))
        
        # 绘制自定义辅助线（如果启用）
        if self.grid_enabled.get():
            xlim = ax.get_xlim()
            ylim = ax.get_ylim()
            
            x_start, x_end = xlim
            y_start, y_end = ylim
            
            # 安全检查：防止间隔过小导致性能问题
            min_interval = 0.1  # 最小间隔
            max_lines = 200  # 每个方向最大辅助线数量
            
            # 绘制垂直辅助线（X方向）
            if self.grid_interval_x >= min_interval:
                x_line_count = 0
                x = 0
                while x <= x_end and x_line_count < max_lines:
                    if x >= x_start:
                        ax.plot([x, x], [y_start, y_end], 
                               color=self.grid_color, 
                               linestyle=self.grid_linestyle,
                               linewidth=self.grid_linewidth,
                               alpha=self.grid_alpha,
                               zorder=0)
                        x_line_count += 1
                    x += self.grid_interval_x
                
                x = -self.grid_interval_x
                while x >= x_start and x_line_count < max_lines:
                    if x <= x_end:
                        ax.plot([x, x], [y_start, y_end], 
                               color=self.grid_color, 
                               linestyle=self.grid_linestyle,
                               linewidth=self.grid_linewidth,
                               alpha=self.grid_alpha,
                               zorder=0)
                        x_line_count += 1
                    x -= self.grid_interval_x
            
            # 绘制水平辅助线（Y方向）
            if self.grid_interval_y >= min_interval:
                y_line_count = 0
                y = 0
                while y <= y_end and y_line_count < max_lines:
                    if y >= y_start:
                        ax.plot([x_start, x_end], [y, y], 
                               color=self.grid_color, 
                               linestyle=self.grid_linestyle,
                               linewidth=self.grid_linewidth,
                               alpha=self.grid_alpha,
                               zorder=0)
                        y_line_count += 1
                    y += self.grid_interval_y
                
                y = -self.grid_interval_y
                while y >= y_start and y_line_count < max_lines:
                    if y <= y_end:
                        ax.plot([x_start, x_end], [y, y], 
                               color=self.grid_color, 
                               linestyle=self.grid_linestyle,
                               linewidth=self.grid_linewidth,
                               alpha=self.grid_alpha,
                               zorder=0)
                        y_line_count += 1
                    y -= self.grid_interval_y
        
        # 绘制演员和道具
        self.render_actors(ax, current_frame, is_export)
        self.render_props(ax, current_frame, is_export)
        
        # 绘制文本框 - 放置在后方备台区域上方且不重合（旧版单一文本框）
        if (current_frame < len(self.text_box["contents"]) and 
            current_frame >= 0 and 
            len(self.text_box["contents"]) > 0):
            text_content = self.text_box["contents"][current_frame]
            if text_content:
                backstage_height = self.stage_height / 8  # 后方备台区域高度
                text_y_position = self.stage_height + backstage_height + 0.5  # 在后方备台区域上方0.5单位
                ax.text(0, text_y_position,
                       text_content,
                       ha='center', va='center',
                       fontsize=self.text_box["font_size"],
                       color='black',
                       bbox=dict(facecolor='white', alpha=0.7, edgecolor='black', pad=5))
        
        # 绘制新版文本框（支持多个独立文本框）
        self.render_textboxes(ax, current_frame, is_export)
        
        # 设置标题
        ax.set_title(f'舞台动画 - 时间: {current_time:.1f}秒', fontsize=14, weight='bold', pad=20)
        
        # 隐藏坐标轴
        ax.set_axis_off()

    def render_styled_name(self, ax, pos, name, default_font_size, default_color, char_styles, is_export=False, rotation=0.0):
        """渲染带字符级样式的名称
        Args:
            ax: matplotlib轴对象
            pos: 位置 (x, y)
            name: 名称文本
            default_font_size: 默认字号
            default_color: 默认颜色
            char_styles: 字符样式列表
            is_export: 是否是导出模式
            rotation: 旋转角度（度）
        """
        # 检查是否有有效的字符样式
        has_valid_styles = (char_styles and len(char_styles) == len(name) and 
                           all(isinstance(s, dict) and "font_size" in s and "color" in s 
                               for s in char_styles))
        
        if not has_valid_styles:
            # 没有样式，使用默认值整体渲染
            ax.text(pos[0], pos[1], name,
                   ha='center', va='center',
                   color=default_color,
                   fontsize=default_font_size,
                   weight='bold',
                   rotation=-rotation)
        else:
            # 检查是否所有字符样式相同
            all_same_style = all(
                s["font_size"] == char_styles[0]["font_size"] and
                s["color"] == char_styles[0]["color"]
                for s in char_styles
            )
            
            if all_same_style:
                # 所有样式相同，整体渲染
                ax.text(pos[0], pos[1], name,
                       ha='center', va='center',
                       color=char_styles[0]["color"],
                       fontsize=char_styles[0]["font_size"],
                       weight='bold',
                       rotation=-rotation)
            else:
                # 多种样式，逐字符绘制
                char_info_list = []
                for j, char in enumerate(name):
                    if j < len(char_styles):
                        char_font_size = char_styles[j].get("font_size", default_font_size)
                        char_color = char_styles[j].get("color", default_color)
                    else:
                        char_font_size = default_font_size
                        char_color = default_color
                    
                    # 计算字符宽度
                    char_width = char_font_size * 0.048
                    char_info_list.append({
                        "char": char,
                        "font_size": char_font_size,
                        "color": char_color,
                        "width": char_width
                    })
                
                # 计算总宽度
                total_width = sum(c["width"] for c in char_info_list)
                
                # 逐字符绘制时应用旋转
                current_x = pos[0] - total_width/2
                for char_info in char_info_list:
                    char_x = current_x + char_info["width"]/2
                    ax.text(char_x, pos[1], char_info["char"],
                           ha='center', va='center',
                           fontsize=char_info["font_size"],
                           color=char_info["color"],
                           weight='bold',
                           rotation=-rotation)
                    current_x += char_info["width"]
    
    def render_actors(self, ax, current_frame, is_export=False):
        """渲染演员
        Args:
            ax: matplotlib轴对象
            current_frame: 当前帧号
            is_export: 是否是导出模式（影响渲染样式）
        """
        for actor in self.actors:
            # 获取当前位置
            if actor["keyframes"]:
                prev_frame = max([f for f in actor["keyframes"] if f <= current_frame], default=None)
                next_frame = min([f for f in actor["keyframes"] if f > current_frame], default=None)
                
                if prev_frame is not None:
                    if next_frame is not None:
                        pos = actor["positions"][current_frame]
                    else:
                        pos = actor["positions"][prev_frame]
                else:
                    pos = actor["positions"][0]
            else:
                pos = actor["positions"][0]
            
            # 获取颜色，如果没有颜色属性则使用默认颜色
            color = actor.get("color", "blue")
            # 获取字号，如果没有字号属性则使用默认字号
            font_size = actor.get("font_size", 10)
            
            # 获取当前帧的名称字符样式
            name_styles_array = actor.get("name_char_styles_per_frame", [])
            char_styles = name_styles_array[current_frame] if current_frame < len(name_styles_array) else []
            
            # 获取当前帧的旋转角度
            rotation = 0.0
            if "rotations" in actor and actor["rotations"]:
                if current_frame < len(actor["rotations"]):
                    rotation = actor["rotations"][current_frame]
            
            # 获取当前帧的样式（新版样式系统）
            if "styles_per_frame" in actor and len(actor["styles_per_frame"]) > current_frame:
                frame_style = actor["styles_per_frame"][current_frame]
                border_color = frame_style.get("border_color", color)
                border_width = frame_style.get("border_width", 2)
                border_style = frame_style.get("border_style", "solid")
                border_alpha = frame_style.get("border_alpha", 1.0)
                fill_enabled = frame_style.get("fill_enabled", False)
                fill_color = frame_style.get("fill_color", color)
                fill_alpha = frame_style.get("fill_alpha", 1.0)
                text_color = frame_style.get("text_color", color)
                text_size = frame_style.get("text_size", font_size)
            else:
                # 向后兼容：使用旧的全局样式
                border_color = color
                border_width = 2
                border_style = "solid"
                border_alpha = 1.0
                fill_enabled = actor.get("fill_enabled", False)
                fill_color = color
                fill_alpha = actor.get("fill_alpha", 1.0)
                text_color = color
                text_size = font_size
            
            # 线形映射
            linestyle_map = {"solid": "-", "dashed": "--", "dotted": ":", "dashdot": "-."}
            linestyle = linestyle_map.get(border_style, "-")
            
            # 检查位置是否在可见区域内（包括舞台和备台区域）
            if self.is_position_in_visible_area(pos):
                if actor["shape"] == "circle":
                    # size是直径，计算半径
                    radius = actor["size"] / 2
                    circle = Circle((pos[0], pos[1]), radius, 
                                 fill=fill_enabled,
                                 facecolor=fill_color if fill_enabled else 'none',
                                 edgecolor=border_color,
                                 alpha=fill_alpha if fill_enabled else border_alpha,
                                 linewidth=border_width,
                                 linestyle=linestyle)
                    # 应用旋转变换（取负号：用户定义正数=顺时针，matplotlib正数=逆时针）
                    t = transforms.Affine2D().rotate_deg_around(pos[0], pos[1], -rotation) + ax.transData
                    circle.set_transform(t)
                    ax.add_patch(circle)
                    # 使用带样式的名称渲染
                    self.render_styled_name(ax, pos, actor["name"], text_size, text_color, char_styles, is_export, rotation)
                elif actor["shape"] == "square":
                    rect = Rectangle((pos[0]-actor["size"]/2, pos[1]-actor["size"]/2),
                                   actor["size"], actor["size"], 
                                   fill=fill_enabled,
                                   facecolor=fill_color if fill_enabled else 'none',
                                   edgecolor=border_color,
                                   alpha=fill_alpha if fill_enabled else border_alpha,
                                   linewidth=border_width,
                                   linestyle=linestyle)
                    # 应用旋转变换（取负号：用户定义正数=顺时针，matplotlib正数=逆时针）
                    t = transforms.Affine2D().rotate_deg_around(pos[0], pos[1], -rotation) + ax.transData
                    rect.set_transform(t)
                    ax.add_patch(rect)
                    # 使用带样式的名称渲染
                    self.render_styled_name(ax, pos, actor["name"], text_size, text_color, char_styles, is_export, rotation)
                elif actor["shape"] == "triangle":
                    triangle = Polygon([(pos[0], pos[1]+actor["size"]),
                                      (pos[0]-actor["size"], pos[1]-actor["size"]),
                                      (pos[0]+actor["size"], pos[1]-actor["size"])], 
                                     fill=fill_enabled,
                                     facecolor=fill_color if fill_enabled else 'none',
                                     edgecolor=border_color,
                                     alpha=fill_alpha if fill_enabled else border_alpha,
                                     linewidth=border_width,
                                     linestyle=linestyle)
                    # 应用旋转变换（取负号：用户定义正数=顺时针，matplotlib正数=逆时针）
                    t = transforms.Affine2D().rotate_deg_around(pos[0], pos[1], -rotation) + ax.transData
                    triangle.set_transform(t)
                    ax.add_patch(triangle)
                    # 使用带样式的名称渲染
                    self.render_styled_name(ax, pos, actor["name"], text_size, text_color, char_styles, is_export, rotation)
    
    def render_props(self, ax, current_frame, is_export=False):
        """渲染道具
        Args:
            ax: matplotlib轴对象
            current_frame: 当前帧号
            is_export: 是否是导出模式（影响渲染样式）
        """
        for prop in self.props:
            # 获取当前位置
            if prop["keyframes"]:
                prev_frame = max([f for f in prop["keyframes"] if f <= current_frame], default=None)
                next_frame = min([f for f in prop["keyframes"] if f > current_frame], default=None)
                
                if prev_frame is not None:
                    if next_frame is not None:
                        pos = prop["positions"][current_frame]
                    else:
                        pos = prop["positions"][prev_frame]
                else:
                    pos = prop["positions"][0]
            else:
                pos = prop["positions"][0]
            
            # 获取颜色，如果没有颜色属性则使用默认颜色
            color = prop.get("color", "red")
            # 获取字号，如果没有字号属性则使用默认字号
            font_size = prop.get("font_size", 10)
            
            # 获取当前帧的名称字符样式
            name_styles_array = prop.get("name_char_styles_per_frame", [])
            char_styles = name_styles_array[current_frame] if current_frame < len(name_styles_array) else []
            
            # 获取当前帧的旋转角度
            rotation = 0.0
            if "rotations" in prop and prop["rotations"]:
                if current_frame < len(prop["rotations"]):
                    rotation = prop["rotations"][current_frame]
            
            # 获取当前帧的样式（新版样式系统）
            if "styles_per_frame" in prop and len(prop["styles_per_frame"]) > current_frame:
                frame_style = prop["styles_per_frame"][current_frame]
                border_color = frame_style.get("border_color", color)
                border_width = frame_style.get("border_width", 2)
                border_style = frame_style.get("border_style", "solid")
                border_alpha = frame_style.get("border_alpha", 1.0)
                fill_enabled = frame_style.get("fill_enabled", False)
                fill_color = frame_style.get("fill_color", color)
                fill_alpha = frame_style.get("fill_alpha", 1.0)
                text_color = frame_style.get("text_color", color)
                text_size = frame_style.get("text_size", font_size)
            else:
                # 向后兼容：使用旧的全局样式
                border_color = color
                border_width = 2
                border_style = "solid"
                border_alpha = 1.0
                fill_enabled = prop.get("fill_enabled", False)
                fill_color = color
                fill_alpha = prop.get("fill_alpha", 1.0)
                text_color = color
                text_size = font_size
            
            # 线形映射
            linestyle_map = {"solid": "-", "dashed": "--", "dotted": ":", "dashdot": "-."}
            linestyle = linestyle_map.get(border_style, "-")
            
            # 检查位置是否在可见区域内（包括舞台和备台区域）
            if self.is_position_in_visible_area(pos):
                if prop["shape"] == "rectangle":
                    rect = Rectangle((pos[0]-prop["width"]/2, pos[1]-prop["height"]/2),
                                   prop["width"], prop["height"], 
                                   fill=fill_enabled,
                                   facecolor=fill_color if fill_enabled else 'none',
                                   edgecolor=border_color,
                                   alpha=fill_alpha if fill_enabled else border_alpha,
                                   linewidth=border_width,
                                   linestyle=linestyle)
                    # 应用旋转变换（取负号：用户定义正数=顺时针，matplotlib正数=逆时针）
                    t = transforms.Affine2D().rotate_deg_around(pos[0], pos[1], -rotation) + ax.transData
                    rect.set_transform(t)
                    ax.add_patch(rect)
                    # 使用带样式的名称渲染
                    self.render_styled_name(ax, pos, prop["name"], text_size, text_color, char_styles, is_export, rotation)
                elif prop["shape"] == "circle":
                    circle = Circle((pos[0], pos[1]), prop["width"]/2, 
                                 fill=fill_enabled,
                                 facecolor=fill_color if fill_enabled else 'none',
                                 edgecolor=border_color,
                                 alpha=fill_alpha if fill_enabled else border_alpha,
                                 linewidth=border_width,
                                 linestyle=linestyle)
                    # 应用旋转变换（取负号：用户定义正数=顺时针，matplotlib正数=逆时针）
                    t = transforms.Affine2D().rotate_deg_around(pos[0], pos[1], -rotation) + ax.transData
                    circle.set_transform(t)
                    ax.add_patch(circle)
                    # 使用带样式的名称渲染
                    self.render_styled_name(ax, pos, prop["name"], text_size, text_color, char_styles, is_export, rotation)
                elif prop["shape"] == "triangle":
                    triangle = Polygon([(pos[0], pos[1]+prop["height"]/2),
                                      (pos[0]-prop["width"]/2, pos[1]-prop["height"]/2),
                                      (pos[0]+prop["width"]/2, pos[1]-prop["height"]/2)], 
                                     fill=fill_enabled,
                                     facecolor=fill_color if fill_enabled else 'none',
                                     edgecolor=border_color,
                                     alpha=fill_alpha if fill_enabled else border_alpha,
                                     linewidth=border_width,
                                     linestyle=linestyle)
                    # 应用旋转变换（取负号：用户定义正数=顺时针，matplotlib正数=逆时针）
                    t = transforms.Affine2D().rotate_deg_around(pos[0], pos[1], -rotation) + ax.transData
                    triangle.set_transform(t)
                    ax.add_patch(triangle)
                    # 使用带样式的名称渲染
                    self.render_styled_name(ax, pos, prop["name"], text_size, text_color, char_styles, is_export, rotation)
    
    def render_textboxes(self, ax, current_frame, is_export=False):
        """渲染新版文本框（支持多个独立文本框）
        Args:
            ax: matplotlib轴对象
            current_frame: 当前帧号
            is_export: 是否是导出模式（影响渲染样式）
        """
        for textbox in self.textboxes:
            # 检查是否在显示时间范围内
            start_frame = textbox.get("start_frame", 0)
            duration_frames = textbox.get("duration_frames", self.total_frames)
            end_frame = start_frame + duration_frames
            
            # 只在时间范围内显示
            if not (start_frame <= current_frame < end_frame):
                continue
            
            # 获取当前位置
            if textbox["keyframes"]:
                prev_frame = max([f for f in textbox["keyframes"] if f <= current_frame], default=None)
                next_frame = min([f for f in textbox["keyframes"] if f > current_frame], default=None)
                
                if prev_frame is not None:
                    if next_frame is not None:
                        pos = textbox["positions"][current_frame]
                    else:
                        pos = textbox["positions"][prev_frame]
                else:
                    pos = textbox["positions"][0]
            else:
                pos = textbox["positions"][0]
            
            # 检查位置是否在可见区域内
            if not self.is_position_in_visible_area(pos):
                continue
            
            # 获取当前帧的内容和字符样式
            contents_array = textbox.get("contents", [])
            char_styles_array = textbox.get("char_styles_per_frame", [])
            
            if current_frame < len(contents_array):
                content = contents_array[current_frame]
            else:
                content = ""
            
            # 如果内容为空，跳过不渲染
            if not content:
                continue
            
            # 获取当前帧的字符样式
            if current_frame < len(char_styles_array):
                char_styles = char_styles_array[current_frame]
            else:
                char_styles = []
            
            # 验证字符样式数组的有效性
            has_valid_styles = False
            if char_styles and len(char_styles) == len(content) and len(char_styles) > 0:
                all_styles_valid = all(
                    isinstance(style, dict) and 
                    "font_size" in style and 
                    "color" in style 
                    for style in char_styles
                )
                has_valid_styles = all_styles_valid
            
            # 检查是否所有字符样式完全相同（提前判断）
            if has_valid_styles:
                first_style = char_styles[0]
                all_same_style = all(
                    s["font_size"] == first_style["font_size"] and 
                    s["color"] == first_style["color"] 
                    for s in char_styles
                )
            else:
                all_same_style = False
            
            # 如果没有样式或所有样式相同，使用整体绘制（避免间距问题）
            if not has_valid_styles or all_same_style:
                # 确定字号和颜色
                if has_valid_styles:
                    use_font_size = char_styles[0]["font_size"]
                    use_color = char_styles[0]["color"]
                else:
                    use_font_size = textbox.get("default_font_size", 12)
                    use_color = textbox.get("default_color", "black")
                
                # 简单模式：整体绘制（统一间距）
                ax.text(pos[0], pos[1],
                       content,
                       ha='center', va='center',
                       fontsize=use_font_size,
                       color=use_color,
                       bbox=dict(facecolor='white', alpha=0.7, edgecolor='gray', pad=5))
            else:
                # 多种样式，逐字符绘制
                char_info_list = []
                max_font_size = 0
                
                for j, char in enumerate(content):
                    if j < len(char_styles):
                        char_font_size = char_styles[j].get("font_size", 12)
                        char_color = char_styles[j].get("color", "black")
                    else:
                        char_font_size = 12
                        char_color = "black"
                    
                    # 计算字符宽度（与实时预览保持一致）
                    char_width = char_font_size * 0.048
                    
                    char_info_list.append({
                        "char": char,
                        "font_size": char_font_size,
                        "color": char_color,
                        "width": char_width
                    })
                    max_font_size = max(max_font_size, char_font_size)
                
                # 计算总宽度
                total_width = sum(c["width"] for c in char_info_list)
                
                # 绘制背景框
                from matplotlib.patches import FancyBboxPatch
                padding = max_font_size * 0.01
                bg_height = max_font_size * 0.025
                bg_bbox = FancyBboxPatch(
                    (pos[0] - total_width/2 - padding, pos[1] - bg_height/2 - padding),
                    total_width + padding*2, bg_height + padding*2,
                    boxstyle="round,pad=0.02", 
                    facecolor='white', alpha=0.7, 
                    edgecolor='gray', linewidth=1)
                ax.add_patch(bg_bbox)
                
                # 逐字符绘制
                current_x = pos[0] - total_width/2
                for char_info in char_info_list:
                    char_x = current_x + char_info["width"]/2
                    ax.text(char_x, pos[1], char_info["char"],
                           ha='center', va='center',
                           fontsize=char_info["font_size"],
                           color=char_info["color"])
                    current_x += char_info["width"]
    
    def is_position_in_stage(self, pos):
        """检查位置是否在舞台区域内"""
        x, y = pos
        return (-self.stage_width/2 <= x <= self.stage_width/2) and (0 <= y <= self.stage_height)
    
    def is_position_in_visible_area(self, pos):
        """检查位置是否在可见区域内（包括舞台、备台区域和文本框区域）"""
        x, y = pos
        invisible_width = self.stage_width / 8  # 左右备台区域宽度
        backstage_height = self.stage_height / 8  # 后方备台区域高度
        
        # 检查X轴范围：包括左右备台区域
        x_in_range = (-self.stage_width/2 - invisible_width <= x <= self.stage_width/2 + invisible_width)
        
        # 检查Y轴范围：与导出视图范围一致（-2 到 stage_height + backstage_height + 1）
        # 包括观众区域、舞台、备台区域和文本框显示区域
        y_in_range = (-2 <= y <= self.stage_height + backstage_height + 1)
        
        return x_in_range and y_in_range

    def on_volume_change(self, value):
        """处理音量变化事件"""
        self.audio_volume = float(value) / 100
        # 连续设置多次确保生效（不使用sleep避免阻塞）
        pygame.mixer.music.set_volume(self.audio_volume)
        pygame.mixer.music.set_volume(self.audio_volume)
        # print(f"🔊 音量: {self.audio_volume:.2f}")  # 可选：显示音量变化

    def on_ruler_toggle(self):
        """处理标尺显示切换事件"""
        if self.ruler_enabled.get():
            # 显示标尺容器
            self.ruler_container.pack(fill=tk.X, padx=5, pady=2, before=self.time_scale)
            # 创建标尺按钮
            self.update_custom_ruler()
            print("✅ 标尺显示已启用")
        else:
            # 隐藏标尺容器
            self.ruler_container.pack_forget()
            # 清除标尺按钮
            self.clear_custom_ruler()
            print("❌ 标尺显示已关闭")
    
    def on_snap_interval_change(self, event=None):
        """处理滑块吸附间隔变化事件"""
        try:
            interval = float(self.snap_interval_entry.get())
            # 四舍五入到小数点后1位
            interval = round(interval, 1)
            
            if interval >= 0.1:  # 确保间隔大于等于0.1秒
                self.snap_interval = interval
                # 更新输入框显示为规范化的值（小数点后1位）
                self.snap_interval_entry.delete(0, tk.END)
                self.snap_interval_entry.insert(0, f"{interval:.1f}")
                print(f"滑块吸附间隔更新为: {interval}秒")
            else:
                # 如果输入不合法（小于0.1秒），恢复到之前的值
                self.snap_interval_entry.delete(0, tk.END)
                self.snap_interval_entry.insert(0, f"{self.snap_interval:.1f}")
                messagebox.showwarning("警告", "滑块吸附间隔不能小于0.1秒")
        except ValueError:
            # 如果输入不是数字，恢复到之前的值
            self.snap_interval_entry.delete(0, tk.END)
            self.snap_interval_entry.insert(0, f"{self.snap_interval:.1f}")
    
    def on_custom_interval_change(self, event=None):
        """处理自定义间隔变化事件"""
        try:
            interval = int(self.custom_interval_entry.get())
            if interval >= 1:  # 确保间隔大于等于1秒
                self.custom_interval = interval
                if self.ruler_enabled.get():
                    self.update_custom_ruler()
                print(f"标尺间隔更新为: {interval}秒")
            else:
                # 如果输入不合法，恢复到之前的值
                self.custom_interval_entry.delete(0, tk.END)
                self.custom_interval_entry.insert(0, str(self.custom_interval))
        except ValueError:
            # 如果输入不是数字，恢复到之前的值
            self.custom_interval_entry.delete(0, tk.END)
            self.custom_interval_entry.insert(0, str(self.custom_interval))
    
    def update_custom_ruler(self):
        """更新自定义模式的标尺显示"""
        # 清除现有标尺
        self.clear_custom_ruler()
        
        # 创建新的标尺按钮
        interval = self.custom_interval
        total_time = int(self.total_seconds)
        
        # 计算标尺按钮的数量和位置
        ruler_times = []
        for t in range(0, total_time + 1, interval):
            if t <= total_time:
                ruler_times.append(t)
        
        # 如果最后一个标尺不是总时长，添加总时长标尺
        if ruler_times and ruler_times[-1] != total_time:
            ruler_times.append(total_time)
        
        # 创建标尺按钮
        for i, time_val in enumerate(ruler_times):
            btn = ttk.Button(self.ruler_frame, text=f"{time_val}s", width=6,
                           command=lambda t=time_val: self.jump_to_time(t))
            btn.pack(side=tk.LEFT, padx=1)
            self.ruler_buttons.append(btn)
        
        print(f"创建了 {len(self.ruler_buttons)} 个标尺按钮，间隔: {interval}秒")
    
    def clear_custom_ruler(self):
        """清除自定义标尺"""
        for btn in self.ruler_buttons:
            btn.destroy()
        self.ruler_buttons.clear()
    
    def jump_to_time(self, target_time):
        """跳转到指定时间"""
        print(f"跳转到时间: {target_time}秒")
        
        # 更新时间轴滑块
        self.time_scale.set(target_time)
        
        # 手动触发时间变化事件
        self.on_time_scale_change(str(target_time))
    
if __name__ == "__main__":
    root = tk.Tk()
    app = StageAnimationTool(root)
    root.mainloop() 